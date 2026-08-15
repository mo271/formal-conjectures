/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import FormalConjecturesUtil

/-!
# Tests for OpaqueLinter
-/

set_option linter.style.opaque_decl true
set_option linter.style.namespace false

/--
warning: Placeholder definitions (e.g., `opaque foo : Type*`) are not allowed.

Note: This linter can be disabled with `set_option linter.style.opaque_decl false`
-/
#guard_msgs(warning) in
opaque MyOpaqueType : Type

#guard_msgs in
def MyNormalType : Type := Nat
