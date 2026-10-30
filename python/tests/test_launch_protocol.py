"""Launch observations require actual entry/return/exit identity."""
import json
import unittest
from cedar_poo_py_test.launch import events


class LaunchProtocolTests(unittest.TestCase):
    def packet(self, success=False, pid=7):
        return (json.dumps({"observation":"native-main-entry","pid":pid})+"\n"+
                json.dumps({"observation":"native-main-return","success":success})+"\nerror\n").encode()

    def test_expected_rejection_keeps_actual_exit(self):
        first, last = events(self.packet(), 7, 1)
        self.assertEqual(first["pid"], 7)
        self.assertFalse(last["success"])

    def test_missing_marker_cannot_qualify_a_launch(self):
        with self.assertRaises(ValueError):
            events(b"manifest error\n", 7, 1)

    def test_wrong_pid_or_exit_or_outcome_cannot_qualify(self):
        for packet, pid, code in ((self.packet(), 8, 1), (self.packet(), 7, 0), (self.packet(True), 7, 1)):
            with self.assertRaises(ValueError):
                events(packet, pid, code)
