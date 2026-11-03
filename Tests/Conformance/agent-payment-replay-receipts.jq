# SPDX-FileCopyrightText: 2026 tao3k team and Contributors
#
# SPDX-License-Identifier: Apache-2.0

length == ($manifest[0].cases | length)
  and all(.[]; .format_version == 1
  and .cedar_policy_version == "4.14.1"
  and .cedar_language_version == "4.6.0"
  and (.policies_sha256 | test("^[0-9a-f]{64}$"))
  and (.entities_sha256 | test("^[0-9a-f]{64}$"))
  and (.request_sha256 | test("^[0-9a-f]{64}$"))
  and .error_free_allow == (.decision == "allow"
  and (.error_policy_ids | length) == 0))
