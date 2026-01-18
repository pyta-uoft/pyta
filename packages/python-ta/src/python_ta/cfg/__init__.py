try:
    from .cfg_generator import generate_cfg
except ModuleNotFoundError:

    def generate_cfg(*_args, **_kwargs) -> None:
        """Dummy version of generate_cfg"""
        raise Exception(
            "This function requires additional dependencies to be installed: " "python_ta[cfg]"
        )


from .graph import *
from .visitor import *
