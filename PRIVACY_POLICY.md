# What data will be sent?
The data that can be sent are the files that you check with PyTA, as well as which errors were caught during the check. These forms of data submission are independent, and optional. If a non-default configuration file was used, this will be sent alongside either of the above data. No identifying information will be sent.

# Who will the data be sent to?
The data will be sent to a server hosted at the University of Toronto in Canada. Researchers at the University of Toronto will have access to the data in order to analyse it.

# How will the data be anonymised?
No identifying information (e.g. username, machine name) is sent to the server. 
A hash of your devices MAC address is sent to identify when an upload comes from the same device, but this in no way identifies the user or device.

# How can I opt in/out?
To change your participation in this research, open your `.pylintrc` configuration file and set the fields `pyta-file-permission` and `pyta-error-permission` to your preference (`yes/no`). The default configuration in the `python_ta` directory is initially set to `no` for both options. Please note that PyTA will use the closest configuration file (directory-wise) to the file being checked.






