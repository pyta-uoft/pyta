import os
import re
from io import StringIO

import pytest

from python_ta import check_all

ESCAPED_SCRIPT = "&quot;&lt;script&gt;alert(2);&lt;/script&gt;&quot;"
UNESCAPED_SCRIPT = "<script>alert(2);</script>"
ESCAPED_MARKDOWN = "&#96; ##world &#96;"
UNESCAPED_MARKDOWN = "</code> ##world <code>"


def clean_response_body(body) -> str:
    """Remove dynamic portions (such as timestamps) from the response body
    before snapshot testing."""
    body = re.sub(r".*<time>.*?</time>.*\n?", "", body)
    body = re.sub(r".*tests[/\\]fixtures[/\\]reporters[/\\]content_injection\.py.*\n?", "", body)
    body = re.sub(
        r".*tests[/\\]fixtures[/\\]reporters[/\\]markdown_escape_script\.py.*\n?", "", body
    )
    body = re.sub(r'\s*<span class="pygments-w">\s*</span>\s*<span', " <span", body)
    body = re.sub(r"localhost:\d+", "localhost:", body)

    return body.strip()


def test_injection(snapshot):
    """Test the HTML injection is properly escaped and is not executed as HTML code"""

    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/content_injection.py")
    )

    buf = StringIO()

    check_all(module_name=script_path, output=buf)

    buf.seek(0)

    response_body = buf.read()
    cleaned_body = clean_response_body(response_body)

    assert ESCAPED_SCRIPT in cleaned_body
    assert UNESCAPED_SCRIPT not in cleaned_body

    snapshot.assert_match(cleaned_body, "script_injection.html")


def test_markdown_escape(snapshot):
    """Test markdown characters in error messages are properly escaped"""

    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/markdown_escape_script.py")
    )

    buf = StringIO()

    check_all(module_name=script_path, output=buf)

    buf.seek(0)

    response_body = buf.read()
    cleaned_body = clean_response_body(response_body)

    assert ESCAPED_MARKDOWN in cleaned_body
    assert UNESCAPED_MARKDOWN not in cleaned_body

    snapshot.assert_match(cleaned_body, "markdown_escape.html")


def _render_report(module_path: str) -> str:
    """Return the HTML report produced for the given module."""
    buf = StringIO()
    check_all(module_name=module_path, output=buf)
    buf.seek(0)
    return buf.read()


@pytest.fixture()
def pinning_report() -> str:
    """Return an HTML report for a file that produces several distinct errors."""
    script_path = os.path.normpath(
        os.path.join(__file__, "../../fixtures/reporters/lsp_reporter_input.py")
    )
    return _render_report(script_path)


def test_every_error_instance_has_a_pin_button(pinning_report):
    """Each reported error can be pinned."""
    instances = re.findall(r'<div class="error-instance"[^>]*>', pinning_report)
    pin_buttons = re.findall(r'<button class="pin-toggle"[^>]*>', pinning_report)

    assert instances, "expected the fixture to report at least one error"
    assert len(pin_buttons) == len(instances)


def test_error_instances_carry_their_message_id(pinning_report):
    """A pin is identified by message id, so every instance must expose one."""
    instances = re.findall(r'<div class="error-instance"[^>]*>', pinning_report)

    for instance in instances:
        assert re.search(r'data-msg-id="[A-Z]\d{4}"', instance), instance


def test_section_carries_the_filename(pinning_report):
    """Pins are keyed by filename so that they survive watch-mode reloads."""
    filenames = re.findall(r'<section id=\d+ data-filename="([^"]+)"', pinning_report)

    assert len(filenames) == 1
    assert filenames[0].endswith("lsp_reporter_input.py")


def test_sidebar_entries_reference_real_error_instances(pinning_report):
    """The sidebar highlights pinned errors by looking up the id it references.

    A stale or misspelled reference would silently break that syncing, so check
    that every reference resolves to an element that actually exists.
    """
    referenced = set(re.findall(r'<li data-pin-ref="([^"]+)"', pinning_report))
    instance_ids = set(re.findall(r'<div class="error-instance" id=([\w-]+)', pinning_report))

    assert referenced, "expected at least one sidebar entry"
    assert referenced == instance_ids


def test_pin_controls_are_present(pinning_report):
    """The filter and summary controls the pinning UI depends on are rendered."""
    for element_id in ("pin-filter", "pin-summary", "pin-summary-text", "clear-pins"):
        assert f'id="{element_id}"' in pinning_report


def test_pin_controls_start_hidden(pinning_report):
    """With no pins stored yet, the filter and summary must not be shown."""
    for element_id in ("pin-filter", "pin-summary"):
        match = re.search(rf'<[^>]*id="{element_id}"[^>]*>', pinning_report)
        assert match is not None
        assert " hidden" in match.group(0), match.group(0)


def test_hidden_attribute_overrides_explicit_display(pinning_report):
    """Elements the filter hides must actually be hidden.

    Several of them set an explicit ``display``, which wins over the user
    agent's rule for the ``hidden`` attribute, so the stylesheet has to
    neutralise it. ``section`` is the easy one to miss: without it, filtering a
    report covering more than one file leaves an empty card behind for every
    file that has no pinned errors.
    """
    match = re.search(r"([^{}]*\[hidden\][^{}]*)\{\s*display:\s*none;\s*\}", pinning_report)

    assert match is not None, "no [hidden] display override found in the report stylesheet"

    selectors = match.group(1)
    for required in (".error-instance[hidden]", "section[hidden]"):
        assert required in selectors, f"{required} missing from the [hidden] override"
