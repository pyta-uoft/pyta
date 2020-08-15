# PyTA Privacy Policy (DRAFT)

Starting in version 1.6.0, PyTA will give user the option of sending anonymized usage data to PyTA maintainers to use to better understand how PyTA is used and to improve the tool.
This will be an optional *opt-in* feature that is not required to use PythonTA.

## What data will be sent?

When PyTA check a file/directory (by calling `python_ta.check_all`), two types of data may be sent:

- The errors detected by PyTA during the check.
- The source files that you ran PyTA on.

These forms of data submission are independent and optional.
If you use a custom PyTA configuration, this information will be sent alongside either of the above data.

## How can I opt in or opt out of this data collection?

To change your participation, open your `.pylintrc` configuration file and set the fields `pyta-file-permission` and `pyta-error-permission` to your preference (`yes` or `no`).
The default configuration in the `python_ta` directory is `no` for both options.

## How will the data be anonymised?

PyTA will not collect or send identifying information about you or your computer. (*Note*: if you choose to submit source files checked by PyTA, those files may contain identifying information about you.)
PyTA does record a hash of your device's MAC address in order to identify when two runs come from the same device, but this is not used to deanonymize the collected data.

## Who will the data be sent to?

The data will be sent to a server hosted at the University of Toronto (Toronto, Canada).
PyTA maintainers and computer science education researchers at the University of Toronto will have access to the data.

## How will this data be used?

This data will be used to better understand how PyTA is used by students for the purpose of making it a better educational tool.
Potential research analyses of collected data include identifying common errors detected by PyTA and identifying errors that persist across multiple PyTA runs.
