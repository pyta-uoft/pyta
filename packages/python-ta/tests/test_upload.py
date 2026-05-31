import hashlib
import json
import uuid
from types import SimpleNamespace

import pytest
import requests

from python_ta.upload import (
    PYTHON_TA_DATA_DIR_ENV_VAR,
    UPLOAD_TIMEOUT_SECONDS,
    _get_anonymous_id,
    _get_anonymous_id_path,
    _get_or_create_local_anonymous_id,
    errors_to_dict,
    get_hashed_id,
    upload_to_server,
)


class FakeResponse:
    def raise_for_status(self) -> None:
        return None


def _make_message(msg_id: str = "E0001") -> SimpleNamespace:
    return SimpleNamespace(
        msg_id=msg_id,
        msg="syntax error",
        symbol="syntax-error",
        module="sample",
        category="error",
        line=1,
    )


@pytest.fixture(autouse=True)
def clear_anonymous_id_cache():
    _get_or_create_local_anonymous_id.cache_clear()
    yield
    _get_or_create_local_anonymous_id.cache_clear()


def test_get_anonymous_id_is_random_and_stable(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    anonymous_id = _get_anonymous_id()
    local_anonymous_id = anonymous_id_file.read_text(encoding="utf-8").strip()

    int(anonymous_id, 16)
    assert len(anonymous_id) == 128
    uuid.UUID(local_anonymous_id)
    assert _get_anonymous_id() == anonymous_id
    assert local_anonymous_id != anonymous_id


def test_get_anonymous_id_prints_save_path(monkeypatch, tmp_path, capsys) -> None:
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    _get_anonymous_id()

    assert f"[INFO] Saved anonymous ID to {tmp_path / 'anonymous_id'}" in capsys.readouterr().out


def test_get_anonymous_id_hashes_locally_stored_id(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    anonymous_id = _get_anonymous_id()
    local_anonymous_id = anonymous_id_file.read_text(encoding="utf-8").strip()

    assert anonymous_id == hashlib.sha512(local_anonymous_id.encode("utf-8")).hexdigest()


def test_get_anonymous_id_uses_valid_stored_id(monkeypatch, tmp_path) -> None:
    local_anonymous_id = str(uuid.uuid4())
    (tmp_path / "anonymous_id").write_text(local_anonymous_id + "\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    assert _get_anonymous_id() == hashlib.sha512(local_anonymous_id.encode("utf-8")).hexdigest()


def test_get_anonymous_id_replaces_invalid_stored_id(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    anonymous_id_file.write_text("not-a-uuid\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    anonymous_id = _get_anonymous_id()
    local_anonymous_id = anonymous_id_file.read_text(encoding="utf-8").strip()

    int(anonymous_id, 16)
    uuid.UUID(local_anonymous_id)
    assert local_anonymous_id != "not-a-uuid"


def test_get_anonymous_id_uses_stable_fallback_when_id_file_is_unwritable(monkeypatch) -> None:
    class FakeParent:
        def mkdir(self, **_kwargs) -> None:
            return None

    class FakePath:
        parent = FakeParent()

        def __str__(self) -> str:
            return "fake-unwritable-id-path"

        def read_text(self, **_kwargs) -> str:
            raise OSError

        def write_text(self, *_args, **_kwargs) -> None:
            raise OSError

    fake_path = FakePath()
    monkeypatch.setattr("python_ta.upload._get_anonymous_id_path", lambda: fake_path)

    anonymous_id = _get_anonymous_id()

    assert _get_anonymous_id() == anonymous_id


def test_get_hashed_id_aliases_anonymous_id(monkeypatch, tmp_path) -> None:
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    with pytest.warns(DeprecationWarning, match="get_hashed_id is deprecated"):
        assert get_hashed_id() == _get_anonymous_id()


def test_get_anonymous_id_path_uses_environment_override(monkeypatch, tmp_path) -> None:
    custom_data_dir = tmp_path / "custom_data"
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(custom_data_dir))

    assert _get_anonymous_id_path() == custom_data_dir / "anonymous_id"


def test_get_anonymous_id_path_uses_platform_data_directory(monkeypatch, tmp_path) -> None:
    monkeypatch.delenv(PYTHON_TA_DATA_DIR_ENV_VAR, raising=False)
    monkeypatch.setattr("python_ta.upload.user_data_path", lambda *_args, **_kwargs: tmp_path)

    assert _get_anonymous_id_path() == tmp_path / "anonymous_id"


def test_errors_to_dict_accepts_current_reporter_messages() -> None:
    message = _make_message()

    assert errors_to_dict([[message]]) == {
        "E0001": [
            {
                "msg_id": "E0001",
                "msg": "syntax error",
                "symbol": "syntax-error",
                "module": "sample",
                "category": "error",
                "line": 1,
            }
        ]
    }


def test_upload_to_server_posts_payload_with_timeout(monkeypatch, tmp_path) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))
    posted = {}

    def fake_post(**kwargs):
        posted.update(kwargs)
        return FakeResponse()

    monkeypatch.setattr("python_ta.upload.requests.post", fake_post)

    upload_to_server(
        errors=[[_make_message()]],
        paths=[str(upload_file)],
        config={"output-format": "pyta-json"},
        url="https://example.com/upload",
        version="1.0.0",
    )

    int(posted["data"]["id"], 16)
    assert len(posted["data"]["id"]) == 128
    assert posted["timeout"] == UPLOAD_TIMEOUT_SECONDS
    assert posted["files"]["0"].closed

    payload = json.loads(posted["data"]["payload"])
    assert payload["cfg"] == {"output-format": "pyta-json"}
    assert payload["errors"]["E0001"][0]["msg"] == "syntax error"


def test_upload_to_server_handles_missing_upload_file(monkeypatch, tmp_path, capsys) -> None:
    missing_file = tmp_path / "missing.py"
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    upload_to_server(
        errors=[],
        paths=[str(missing_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert "Could not read a file selected for upload" in capsys.readouterr().out


def test_upload_to_server_handles_timeout(monkeypatch, tmp_path, capsys) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    def fake_post(**_kwargs):
        raise requests.Timeout

    monkeypatch.setattr("python_ta.upload.requests.post", fake_post)

    upload_to_server(
        errors=[],
        paths=[str(upload_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert "Connection timed out" in capsys.readouterr().out


def test_upload_to_server_handles_forbidden_response(monkeypatch, tmp_path, capsys) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    class ForbiddenResponse:
        def raise_for_status(self) -> None:
            response = SimpleNamespace(status_code=403)
            raise requests.HTTPError(response=response)

    monkeypatch.setattr("python_ta.upload.requests.post", lambda **_kwargs: ForbiddenResponse())

    upload_to_server(
        errors=[],
        paths=[str(upload_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert "HTTP Response Status 403" in capsys.readouterr().out


@pytest.mark.parametrize(
    ("status_code", "expected_message"),
    [
        (400, "HTTP Response Status 400"),
        (500, "HTTP Response Status 500"),
        (503, "HTTP Response Status 503"),
    ],
)
def test_upload_to_server_handles_http_error_responses(
    monkeypatch, tmp_path, capsys, status_code: int, expected_message: str
) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    class ErrorResponse:
        def raise_for_status(self) -> None:
            response = SimpleNamespace(status_code=status_code)
            raise requests.HTTPError(response=response)

    monkeypatch.setattr("python_ta.upload.requests.post", lambda **_kwargs: ErrorResponse())

    upload_to_server(
        errors=[],
        paths=[str(upload_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert expected_message in capsys.readouterr().out


def test_upload_to_server_handles_http_error_without_response(
    monkeypatch, tmp_path, capsys
) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    class ErrorResponse:
        def raise_for_status(self) -> None:
            raise requests.HTTPError("server failed")

    monkeypatch.setattr("python_ta.upload.requests.post", lambda **_kwargs: ErrorResponse())

    upload_to_server(
        errors=[],
        paths=[str(upload_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert 'Error message: "server failed"' in capsys.readouterr().out


def test_upload_to_server_handles_request_exception(monkeypatch, tmp_path, capsys) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))

    def fake_post(**_kwargs):
        raise requests.RequestException("request failed")

    monkeypatch.setattr("python_ta.upload.requests.post", fake_post)

    upload_to_server(
        errors=[],
        paths=[str(upload_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert 'Error message: "request failed"' in capsys.readouterr().out


def test_upload_to_server_posts_empty_files_and_serializes_config_values(
    monkeypatch, tmp_path
) -> None:
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))
    posted = {}

    def fake_post(**kwargs):
        posted.update(kwargs)
        return FakeResponse()

    monkeypatch.setattr("python_ta.upload.requests.post", fake_post)

    upload_to_server(
        errors=[],
        paths=[],
        config={"path": tmp_path},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert posted["files"] == {}
    payload = json.loads(posted["data"]["payload"])
    assert payload == {"errors": {}, "cfg": {"path": str(tmp_path)}}


def test_upload_to_server_closes_files_when_request_fails(monkeypatch, tmp_path, capsys) -> None:
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(PYTHON_TA_DATA_DIR_ENV_VAR, str(tmp_path))
    posted = {}

    def fake_post(**kwargs):
        posted.update(kwargs)
        raise requests.ConnectionError

    monkeypatch.setattr("python_ta.upload.requests.post", fake_post)

    upload_to_server(
        errors=[],
        paths=[str(upload_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert posted["files"]["0"].closed
    assert "[ERROR] Upload failed" in capsys.readouterr().out
