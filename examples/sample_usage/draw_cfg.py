import python_ta.cfg.cfg_generator as cfg_generator

USAGE = "USAGE: python -m examples.sample_usage.draw_cfg <your-file.py>"


def main(filepath: str) -> None:
    cfg_generator.generate_cfg(mod=filepath, auto_open=True)


if __name__ == "__main__":
    import sys

    if len(sys.argv) < 2:
        print(USAGE)
        exit(1)

    filepath = sys.argv[1]
    main(filepath)
