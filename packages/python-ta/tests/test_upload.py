import hashlib
import json
import uuid
from types import SimpleNamespace

import requests

from python_ta.upload import (
    ANONYMOUS_ID_ENV_VAR,
    UPLOAD_TIMEOUT_SECONDS,
    errors_to_dict,
    get_anonymous_id,
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


def test_get_anonymous_id_is_random_and_stable(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

    anonymous_id = get_anonymous_id()
    local_anonymous_id = anonymous_id_file.read_text(encoding="utf-8").strip()

    int(anonymous_id, 16)
    assert len(anonymous_id) == 128
    uuid.UUID(local_anonymous_id)
    assert get_anonymous_id() == anonymous_id
    assert local_anonymous_id != anonymous_id


def test_get_anonymous_id_hashes_locally_stored_id(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

    anonymous_id = get_anonymous_id()
    local_anonymous_id = anonymous_id_file.read_text(encoding="utf-8").strip()

    assert anonymous_id == hashlib.sha512(local_anonymous_id.encode("utf-8")).hexdigest()


def test_get_anonymous_id_replaces_invalid_stored_id(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    anonymous_id_file.write_text("not-a-uuid\n", encoding="utf-8")
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

    anonymous_id = get_anonymous_id()
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

    monkeypatch.setattr("python_ta.upload._cached_local_anonymous_id", None)
    monkeypatch.setattr("python_ta.upload._get_anonymous_id_path", lambda: FakePath())

    anonymous_id = get_anonymous_id()

    assert get_anonymous_id() == anonymous_id


def test_get_hashed_id_aliases_anonymous_id(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

    assert get_hashed_id() == get_anonymous_id()


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


def test_errors_to_dict_accepts_legacy_message_sets() -> None:
    message = _make_message("C0301")
    message_set = SimpleNamespace(
        code={},
        style={"C0301": SimpleNamespace(messages=[message])},
    )

    assert errors_to_dict([message_set])["C0301"][0]["symbol"] == "syntax-error"


def test_upload_to_server_posts_payload_with_timeout(monkeypatch, tmp_path) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))
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
    anonymous_id_file = tmp_path / "anonymous_id"
    missing_file = tmp_path / "missing.py"
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

    upload_to_server(
        errors=[],
        paths=[str(missing_file)],
        config={},
        url="https://example.com/upload",
        version="1.0.0",
    )

    assert "Could not read a file selected for upload" in capsys.readouterr().out


def test_upload_to_server_handles_timeout(monkeypatch, tmp_path, capsys) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

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
    anonymous_id_file = tmp_path / "anonymous_id"
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))

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


def test_upload_to_server_closes_files_when_request_fails(monkeypatch, tmp_path, capsys) -> None:
    anonymous_id_file = tmp_path / "anonymous_id"
    upload_file = tmp_path / "sample.py"
    upload_file.write_text("print('hello')\n", encoding="utf-8")
    monkeypatch.setenv(ANONYMOUS_ID_ENV_VAR, str(anonymous_id_file))
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
