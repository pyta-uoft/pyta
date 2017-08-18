def generic_catch() -> None:
    try:
        a = 5 / 0
    except Exception:
        print('Got exception')
