try:
    from .cfg_generator import generate_cfg
except ModuleNotFoundError:

    def generate_cfg(
        mod: str = "",
        auto_open: bool = False,
        visitor_options: Optional[dict[str, Any]] = None,
        z3_enabled: bool = False,
    ) -> None:
        """Dummy version of generate_cfg"""
        raise Exception(
            "This function requires additional dependencies to be installed: " "python_ta[cfg]"
        )


from .graph import *
from .visitor import *
