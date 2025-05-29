#!/bin/bash
# Copyright 2025 Google LLC

# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at

#     https://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


# A script to check for a copyright header in all .lean files.
# It checks that the file starts with the header and allows for any 4-digit year.

# --- IMPORTANT ---
# This script requires GNU grep, which supports the -P (Perl Regex) and -z (null-delimited) flags.
# On macOS, the default `grep` is BSD grep and will not work.
# If you are on macOS, install GNU grep with Homebrew: `brew install grep`
# Then, change the `grep` command below to `ggrep`.


# Define the header in a readable multiline block. ---
# All special regex characters like `.` and `()` must be escaped with a `\`.
read -r -d '' header_block <<'EOF'
/-
Copyright 2[0-9]{3} Google LLC

Licensed under the Apache License, Version 2\.0 \(the "License"\);
you may not use this file except in compliance with the License\.
You may obtain a copy of the License at

    https://www\.apache\.org/licenses/LICENSE-2\.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied\.
See the License for the specific language governing permissions and
limitations under the License\.
-/
EOF


# Convert literal newlines into the `\n` sequence for grep. ---
# This uses bash parameter expansion to replace every newline (`$'\n'`)
# with the two-character string `\n` (`\\n`).
# The result is the pattern that `grep -Pz` can understand.
expected_pattern="${header_block//$'\n'/\\n}"


echo "🔍 Checking for copyright headers in .lean files (ignoring hidden directories)..."

error_found=false
files_checked=0

# Use process substitution to avoid creating a subshell for the while loop.
# This ensures that the `files_checked` variable is correctly incremented in the main script.
while IFS= read -r -d $'\0' file; do
  files_checked=$((files_checked+1))

  # Use `grep` for Linux environments like GitHub Actions.
  # (Locally on macOS, you would use `ggrep`).
  if ! grep -qPz "$expected_pattern" "$file"; then
    echo "❌ Error: The file '$file' does not start with a valid copyright header."
    error_found=true
  fi
done < <(find . -type f -name "*.lean" -not -path '*/.*' -print0)


echo "--------------------------------------------------"

# Final logic block to determine success or failure.

# 1. Check if no files were found.
if [ "$files_checked" -eq 0 ]; then
  echo "🔴 Error: No .lean files were found to check."
  exit 1
fi

# 2. Check for header errors found during the loop.
if [ "$error_found" = true ]; then
  echo "🔴 Some files are missing their copyright headers."
  exit 1
fi

# 3. If we get here, everything is okay.
echo "✅ All $files_checked files checked have a valid copyright header."
exit 0
