"""Clock ABI/protocol tests only; no policy or resource acceptance logic."""
import sys
import unittest
from unittest.mock import patch
from cedar_poo_py_test.clock_anchor import clock_anchor


class ClockAnchorTests(unittest.TestCase):
    def test_unsupported_clock_is_absent(self):
        with patch("cedar_poo_py_test.clock_anchor.sys.platform", "linux"):
            self.assertIsNone(clock_anchor())

    @unittest.skipUnless(sys.platform == "darwin", "Darwin clock ABI")
    def test_real_clock_anchor_has_valid_brackets(self):
        anchor = clock_anchor()
        self.assertIsNotNone(anchor)
        self.assertGreater(anchor["numer"], 0)
        self.assertGreater(anchor["denom"], 0)
        self.assertGreater(anchor["absolute_ticks"], 0)
        self.assertGreaterEqual(anchor["continuous_ticks"], anchor["absolute_ticks"])
        self.assertLessEqual(anchor["unix_before_ns"], anchor["unix_after_ns"])
        self.assertLessEqual(anchor["monotonic_before_ns"], anchor["monotonic_after_ns"])
