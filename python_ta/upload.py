import uuid
import hashlib
import requests
import json


def errors_to_json(errors):
    """Convert PyTA errors from MessageSet format to json."""
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
                    info = {k: getattr(msg, k) for k in error_info}
                    err_as_dict[key].append(info)
    return json.dumps(err_as_dict)


def upload_to_server(errors, config, url, default, version, time, paths=None):
    """Send POST request to server with formatted data."""
    unique_id = hash_uuid(str(uuid.uuid1())[24:])  # Hashing just the mac address portion of the uuid
    files = []
    if paths:
        for path in paths:
            f = open(path, 'rb')
            files.append(f)
    upload = {str(i): f for i, f in enumerate(files)}  # requests.post() requires passing a dict
    # upload is an empty dict in the case that paths is empty
    if config != default:  # Need to clarify; 'default' currently refers to the config file in ../pyta.
        # This is a path comparison, not an option comparison.
        cfg = open(config, 'rb')
        upload['config'] = cfg
    json_errors = errors_to_json(errors)
    try:
        response = requests.post(
            url=url,
            files=upload,
            data={'id': unique_id,
                  'version': version,
                  'time': time,
                  'errors': json_errors
                  }
        )
        response.raise_for_status()
    except requests.HTTPError as e:
        print('[ERROR] Upload failed')
        if e.response.status_code == 400:
            print('[ERROR] HTTP Response Status 400: Client-side error, likely due to improper syntax. '
                  'Please report this to your instructor (and attach the code that caused the error).')
            raise e
        elif e.response.status_code == 403:
            print('[ERROR] HTTP Response Status 403: Authorization is currently required for submission.')
            raise e
        elif e.response.status_code == 500:
            print('[ERROR] HTTP Response Status 500: The server ran into a situation it doesn\'t know how to handle. ')
            print('Please report this to your instructor (and attach the code that caused the error).' )
            raise e
        elif e.response.status_code == 503:
            print('[ERROR] HTTP Response Status 503: The server is not ready to handle your request. ')
            print('It may be down for maintenance.')
            raise e
        else:
            print('[ERROR] Error message: "{}"'.format(e))
            raise e
    except requests.ConnectionError as e:
        print('[ERROR] Upload failed')
        print('[ERROR] Error message: Connection timed out. This may be caused by your firewall, or the server may be '
              'temporarily down.')
    for f in files:  # Closing files after uploading
        f.close()


def hash_uuid(uid):
    """
    Hashes a given string. Used for the user's mac-address
    for privacy protection.
    """
    hash_gen = hashlib.sha512()
    encoded = uid.encode('utf-8')
    hash_gen.update(encoded)
    return hash_gen.hexdigest()
