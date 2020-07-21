import uuid
import hashlib
import requests
import json
from typing import Dict, List, NamedTuple


def errors_to_dict(errors: List[NamedTuple]) -> Dict[str, List[str]]:
    """Convert PyTA errors from MessageSet format to a json format Dictionary."""
    error_info = ['msg_id', 'msg', 'symbol', 'module', 'category', 'line']
    error_types = ['code', 'style']
    err_as_dict = {}
    for msg_set in errors:  # This iterates over the (filename, code, style) MessageSets
        for error_type in error_types:  # This iterates over the code and style attributes
            current_type = getattr(msg_set, error_type)  # Gets either the code or style dictionary
            for key in current_type.keys():  # Iterates over the error id's of caught errors
                err_as_dict[key] = []
                info_set = current_type.get(key)
                for msg in info_set.messages:  # Iterates over the messages for each error of the given code
                    err_as_dict[key].append({k: getattr(msg, k) for k in error_info})
    return err_as_dict


def upload_to_server(errors: List[NamedTuple], paths: List[str], config: Dict[str, str], url: str, version: str) -> None:
    """Send POST request to server with formatted data."""
    unique_id = get_hashed_id()  # Generates a device-specific ID
    files = []
    for path in paths:
        f = open(path)
        files.append(f)
    upload = {str(i): f for i, f in enumerate(files)}  # requests.post() requires passing a dict
    # 'upload' is an empty dict in the case that 'files' is empty
    errors_dict = errors_to_dict(errors)
    to_json = {'errors': errors_dict}
    if config:  # 'config' is an empty dictionary if the default was used
        to_json['cfg'] = config
    payload = json.dumps(to_json)
    try:
        response = requests.post(
            url=url,
            files=upload,
            data={'id': unique_id,
                  'version': version,
                  'payload': payload
                  }
        )
        for f in files:
            f.close()
        response.raise_for_status()
        print('[INFO] Upload successful')
    except requests.HTTPError as e:
        print('[ERROR] Upload failed')
        if e.response.status_code == 400:
            print('[ERROR] HTTP Response Status 400: Client-side error, likely due to improper syntax. '
                  'Please report this to your instructor (and attach the code that caused the error).')
        elif e.response.status_code == 403:
            print('[ERROR] HTTP Response Status 403: Authorization is currently required for submission.')
        elif e.response.status_code == 500:
            print('[ERROR] HTTP Response Status 500: The server ran into a situation it doesn\'t know how to handle. ')
            print('Please report this to your instructor (and attach the code that caused the error).' )
        elif e.response.status_code == 503:
            print('[ERROR] HTTP Response Status 503: The server is not ready to handle your request. ')
            print('It may be down for maintenance.')
        else:
            print('[ERROR] Error message: "{}"'.format(e))

    except requests.ConnectionError as e:
        print('[ERROR] Upload failed')
        print('[ERROR] Error message: Connection timed out. This may be caused by your firewall, or the server may be '
              'temporarily down.')


def get_hashed_id() -> str:
    """
    Generates a unique ID by hashing the user's mac-address.
    """
    mac = str(uuid.uuid1())[24:]
    hash_gen = hashlib.sha512()
    encoded = mac.encode('utf-8')
    hash_gen.update(encoded)
    return hash_gen.hexdigest()
