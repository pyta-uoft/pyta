from unittest.mock import patch

import python_ta


@patch("webbrowser.open", return_value=None)
def open_server(mock_webbrowser_open):
    python_ta.check_all(
        config={
            "watch": True,
        }
    )


open_server()
