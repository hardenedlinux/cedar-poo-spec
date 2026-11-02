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


class MachEventIntervalTests(unittest.TestCase):
    def test_explicit_domains_and_fractional_ticks_keep_bracket_uncertainty(self):
        from cedar_poo_py_test.clock_anchor import mach_event_interval
        anchor = {"numer": 125, "denom": 3, "monotonic_before_ns": 10000,
                  "monotonic_after_ns": 10002, "absolute_ticks": 100, "continuous_ticks": 200}
        self.assertEqual(mach_event_interval(anchor, 101, "absolute"), (10041, 10044))
        self.assertEqual(mach_event_interval(anchor, 101, "continuous"), (5875, 5877))
        self.assertEqual(mach_event_interval(anchor, 100, "absolute"), (10000, 10002))

    def test_missing_domain_and_malformed_anchors_cannot_silently_produce_latency(self):
        from cedar_poo_py_test.clock_anchor import mach_event_interval
        anchor = {"numer": 125, "denom": 3, "monotonic_before_ns": 10000,
                  "monotonic_after_ns": 10002, "absolute_ticks": 100}
        for domain in ("wall", "guess", "continuous"):
            with self.assertRaises(ValueError):
                mach_event_interval(anchor, 101, domain)
        for update in ({"denom": 0}, {"numer": -1}, {"monotonic_after_ns": 9999},
                       {"absolute_ticks": -1}, {"numer": 125.0}):
            with self.assertRaises(ValueError):
                mach_event_interval(anchor | update, 101, "absolute")
        for ticks in (-1, 101.0, True):
            with self.assertRaises(ValueError):
                mach_event_interval(anchor, ticks, "absolute")
