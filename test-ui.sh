#!/bin/bash
# generate-example-report.sh

SNAPSHOT_PATH="/Users/lxyhan/pyta/tests/test_reporters/test_html_server.py"

echo "Generating example web reporter..."
python -c "import python_ta; python_ta.check_all('examples.custom_checkers.e9999_forbidden_import')"

echo "Example report generated!"
echo ""
read -p "Update snapshot tests? (y/n): " -n 1 -r
echo ""

if [[ $REPLY =~ ^[Yy]$ ]]; then
    echo "Updating snapshots..."
    pytest --snapshot-update "$SNAPSHOT_PATH"
    echo "Snapshots updated!"
else
    echo "Skipping snapshot update."
fi
