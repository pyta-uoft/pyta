from unittest.mock import patch

from python_ta.__init__ import check_all


@patch("webbrowser.open", return_value=None)
def open_server(mock_webbrowser_open):
    print("GITHUB ACTIONS HAS FOUND THE PATH")
    check_all(
        config={
            "watch": True,
            "pyta_port": 5008,
        }
    )


open_server()
