"""Typed process adapter for the Rust bridge's current JSON CLI."""

from dataclasses import dataclass
from pathlib import Path
import subprocess
from typing import Sequence


class BridgeError(RuntimeError):
    """A Rust bridge command failed without producing an admitted receipt."""


DEFAULT_COMMAND = (
    "cargo", "run", "--locked", "--quiet", "-p", "cedar-poo-bridge",
    "--manifest-path", "Cargo.toml", "--",
)


@dataclass(frozen=True)
class RustBridge:
    repository: Path
    command: tuple[str, ...] = DEFAULT_COMMAND

    def run(
        self,
        operation: str | None = None,
        *,
        arguments: Sequence[str] = (),
        input_file: Path | None = None,
        output_file: Path | None = None,
    ) -> bytes:
        """Run one bridge operation, preserving its exact stdin and stdout bytes."""
        command = [*self.command]
        if operation is not None:
            command.append(operation)
        command.extend(arguments)
        data = input_file.read_bytes() if input_file is not None else None
        result = subprocess.run(
            command, cwd=self.repository, input=data, capture_output=True, check=False,
        )
        if result.returncode != 0:
            detail = result.stderr.decode("utf-8", errors="replace").strip()
            raise BridgeError(f"Rust bridge {operation or 'default'} failed ({result.returncode}): {detail}")
        if output_file is not None:
            output_file.parent.mkdir(parents=True, exist_ok=True)
            output_file.write_bytes(result.stdout)
        return result.stdout
