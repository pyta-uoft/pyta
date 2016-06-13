def repeat_except_blocks():
    try:
        raise Exception()
    except Exception:
        print('This is triggered')
    except Exception:
        print('Duplicate exception block')
