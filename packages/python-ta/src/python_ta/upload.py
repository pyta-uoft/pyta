from __future__ import annotations

import hashlib
import json
import os
import sys
import uuid
from contextlib import ExitStack
from pathlib import Path
from typing import Any, Iterable

import requests

UPLOAD_TIMEOUT_SECONDS = 5
ANONYMOUS_ID_ENV_VAR = "PYTA_ANONYMOUS_ID_FILE"
_cached_local_anonymous_id: tuple[str, str] | None = None


def errors_to_dict(errors: Iterable[Any]) -> dict[str, list[dict[str, Any]]]:
    """Convert PyTA errors from MessageSet format to a json format Dictionary."""
    error_info = ["msg_id", "msg", "symbol", "module", "category", "line"]
    err_as_dict = {}
    for msg in _iter_error_messages(errors):
        msg_id = getattr(msg, "msg_id", None)
        if msg_id is None:
            continue
        err_as_dict.setdefault(msg_id, []).append(
            {field: getattr(msg, field, None) for field in error_info}
        )
    return err_as_dict


def upload_to_server(
    errors: Iterable[Any], paths: list[str], config: dict[str, Any], url: str, version: str
) -> None:
    """Send POST request to server with formatted data."""
    unique_id = get_anonymous_id()
    errors_dict = errors_to_dict(errors)
    to_json = {"errors": errors_dict}
    if config:  # 'config' is an empty dictionary if the default was used
        to_json["cfg"] = config
    payload = json.dumps(to_json, default=str)

    try:
        with ExitStack() as stack:
            upload = {
                str(i): stack.enter_context(open(path, "rb")) for i, path in enumerate(paths)
            }
            response = requests.post(
                url=url,
                files=upload,
                data={"id": unique_id, "version": version, "payload": payload},
                timeout=UPLOAD_TIMEOUT_SECONDS,
            )
        response.raise_for_status()
        print("[INFO] Upload successful")
    except OSError as e:
        print("[ERROR] Upload failed")
        print(f'[ERROR] Could not read a file selected for upload: "{e}"')
    except requests.HTTPError as e:
        print("[ERROR] Upload failed")
        status_code = e.response.status_code if e.response is not None else None
        if status_code == 400:
            print(
                "[ERROR] HTTP Response Status 400: Client-side error, likely due to improper syntax. "
                "Please report this to your instructor (and attach the code that caused the error)."
            )
        elif status_code == 403:
            print(
                "[ERROR] HTTP Response Status 403: Authorization is currently required for submission."
            )
        elif status_code == 500:
            print(
                "[ERROR] HTTP Response Status 500: The server ran into a situation it doesn't know how to handle. "
            )
            print(
                "Please report this to your instructor (and attach the code that caused the error)."
            )
        elif status_code == 503:
            print(
                "[ERROR] HTTP Response Status 503: The server is not ready to handle your request. "
            )
            print("It may be down for maintenance.")
        else:
            print('[ERROR] Error message: "{}"'.format(e))
    except requests.Timeout:
        print("[ERROR] Upload failed")
        print("[ERROR] Error message: Connection timed out. The server may be temporarily down.")
    except requests.ConnectionError:
        print("[ERROR] Upload failed")
        print(
            "[ERROR] Error message: Could not connect. This may be caused by your firewall, or the server may be "
            "temporarily down."
        )
    except requests.RequestException as e:
        print("[ERROR] Upload failed")
        print('[ERROR] Error message: "{}"'.format(e))


def get_anonymous_id() -> str:
    """Return an anonymous ID for opt-in data uploads.

    This is a hash of a random local ID so multiple opt-in uploads can be
    grouped without deriving an identifier from hardware information.
    """
    local_anonymous_id = _get_or_create_local_anonymous_id()
    return hashlib.sha512(local_anonymous_id.encode("utf-8")).hexdigest()


def get_hashed_id() -> str:
    """Return the anonymous upload ID.

    This function is kept as a backwards-compatible alias for older code that
    imported it directly.
    """
    return get_anonymous_id()


def _get_or_create_local_anonymous_id() -> str:
    """Return the random local ID used as input for the anonymous upload ID."""
    global _cached_local_anonymous_id

    anonymous_id_path = _get_anonymous_id_path()
    anonymous_id_path_key = str(anonymous_id_path)
    if (
        _cached_local_anonymous_id is not None
        and _cached_local_anonymous_id[0] == anonymous_id_path_key
    ):
        return _cached_local_anonymous_id[1]

    try:
        anonymous_id = anonymous_id_path.read_text(encoding="utf-8").strip()
        uuid.UUID(anonymous_id)
        return anonymous_id
    except (OSError, ValueError):
        anonymous_id = str(uuid.uuid4())

    try:
        anonymous_id_path.parent.mkdir(parents=True, exist_ok=True)
        anonymous_id_path.write_text(anonymous_id + "\n", encoding="utf-8")
    except OSError:
        _cached_local_anonymous_id = (anonymous_id_path_key, anonymous_id)
    return anonymous_id


def _iter_error_messages(errors: Iterable[Any]) -> Iterable[Any]:
    """Yield individual messages from current and legacy reporter upload data."""
    for error_group in errors:
        if isinstance(error_group, list):
            yield from error_group
        elif hasattr(error_group, "code") and hasattr(error_group, "style"):
            for error_type in ("code", "style"):
                current_type = getattr(error_group, error_type)
                for info_set in current_type.values():
                    yield from info_set.messages
        else:
            yield error_group


def _get_anonymous_id_path() -> Path:
    """Return the local path used to store the anonymous upload ID."""
    if ANONYMOUS_ID_ENV_VAR in os.environ:
        return Path(os.environ[ANONYMOUS_ID_ENV_VAR]).expanduser()

    if sys.platform == "win32" and os.environ.get("APPDATA"):
        return Path(os.environ["APPDATA"]) / "PythonTA" / "anonymous_id"
    return Path.home() / ".python_ta" / "anonymous_id"
