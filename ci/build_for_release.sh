#!/bin/bash

# Get the directory of the current script
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Set environment variables
export CMAKE_BUILD_TYPE="Release"
export PARALLEL="OFF"
export ENABLE_LINE_EDITING="FALSE"

# Call helper_script.sh using its absolute path
"$SCRIPT_DIR/build_maximally_static.sh"
