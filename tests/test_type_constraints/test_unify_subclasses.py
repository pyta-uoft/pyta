import test_unify

raise SkipTest(skip_msg)


def test_subclasses():
    unify_helper(int, bool, bool)
    unify_helper(bool, int, bool)


def test_one_typevar_bool_int():
    raise SkipTest("skip_msg")
    tc.reset()
    tv = setup_typevar(bool)

    resolve_helper(tv, bool)
    unify_helper(tv, int, bool)
    unify_helper(int, tv, bool)
    unify_helper(tv, str, error_msg)


def test_tuple_subclass():
    raise SkipTest(skip_msg)
    unify_helper(Tuple[bool, bool], Tuple[int, int], Tuple[bool, bool])
    unify_helper(Tuple[int, int], Tuple[bool, bool], Tuple[bool, bool])


def test_callable_subclass():
    raise SkipTest(skip_msg)
    c1 = Callable[[bool], bool]
    c2 = Callable[[int], int]

    unify_helper(c1, c2, c1)
    unify_helper(c2, c1, c1)
