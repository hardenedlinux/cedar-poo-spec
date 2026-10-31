"""Dependency boundaries use Cargo package identities, not checkout paths."""
import unittest
from cedar_poo_py_test.rust_checks import dependency_names


class DependencyIdentityTests(unittest.TestCase):
    def test_source_paths_cannot_create_dependency_names(self):
        names = dependency_names(
            "cedar-poo-core v0.1.0 (/tmp/cedar-policy-preparation/rust/core)\n"
            "serde v1.0.0 (/tmp/mrr-data/p256 v/example)\n"
        )
        self.assertEqual(names, {"cedar-poo-core", "serde"})

    def test_real_direct_and_transitive_packages_remain_visible(self):
        names = dependency_names(
            "cedar-poo-core v0.1.0 (/tmp/project)\n"
            "cedar-policy v4.12.0\n"
            "cedar-policy-core v4.12.0 (*)\n"
            "p256 v0.13.2\n"
            "mrr-data-content v0.1.0 (https://example.invalid/repo#123)\n"
        )
        self.assertTrue(any(name.startswith("cedar-policy") for name in names))
        self.assertIn("p256", names)
        self.assertTrue(any(name.startswith("mrr-data") for name in names))
