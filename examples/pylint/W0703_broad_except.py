def generic_catch():
    try:
        a = 5 / 0
    except Exception:
        print('Got exception')
