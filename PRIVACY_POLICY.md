# PyTA Privacy Policy (DRAFT)

Starting in version 1.6.0, PyTA will give user the option of sending anonymized usage data to PyTA maintainers to use to better understand how PyTA is used and to improve the tool.
This will be an optional _opt-in_ feature that is not required to use PythonTA.

## What data will be sent?

When PyTA checks a file/directory (by calling `python_ta.check_all`), two types of data may be sent:

- The errors detected by PyTA during the check.
- The source files that you ran PyTA on.

These forms of data submission are independent and optional.
If you use a custom PyTA configuration, this information will be sent alongside either of the above data.
Each upload also includes the PythonTA version and an anonymous client ID used to group opt-in submissions.

## How can I opt in or opt out of this data collection?

To change your participation, open your `.pylintrc` configuration file and set the fields `pyta-file-permission` and `pyta-error-permission` to your preference (`yes` or `no`).
The default configuration in the `python_ta` directory is `no` for both options.

## How will the data be anonymised?

PyTA will not collect or send identifying information about you or your computer. (_Note_: if you choose to submit source files checked by PyTA, those files may contain identifying information about you.)
PyTA does not derive its anonymous client ID from hardware identifiers such as your device's MAC address.
Instead, when data is first submitted, PyTA generates a random ID and stores it locally.
Future opt-in submissions include a hash of this random ID, allowing submissions to be grouped without sending the locally stored ID itself.
On Windows this is stored in `%APPDATA%\PythonTA\anonymous_id`; on other platforms it is stored in `~/.python_ta/anonymous_id`.
Deleting this file resets the anonymous ID.

## Who will the data be sent to?

The data will be sent to a server hosted at the University of Toronto (Toronto, Canada).
PyTA maintainers and computer science education researchers at the University of Toronto will have access to the data.

## How will this data be used?

This data will be used to better understand how PyTA is used by students for the purpose of making it a better educational tool.
Potential research analyses of collected data include identifying common errors detected by PyTA and identifying errors that persist across multiple PyTA runs associated with the same anonymous ID.
