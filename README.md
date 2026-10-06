# json2dir in Lean 4

This is a Lean 4 implementation of the [`json2dir` CLI](https://github.com/alurm/json2dir).
It reads a JSON object from standard input and creates its directory tree in the
current directory:

- Objects create directories.
- Strings create UTF-8 files.
- `["link", target]` creates a symbolic link.
- `["script", content]` creates a file and sets its executable bits.

Build with Lean 4.30.0 and a C compiler available on `PATH`:

```sh
lake build
```

Run it in the directory where files should be created:

```sh
.lake/build/bin/json2dir < sample.json
```

The executable uses the POSIX `ln` and `chmod` commands for links and executable
files. It takes no command-line arguments. Invalid JSON, invalid entries, and
filesystem errors are printed to standard error and produce a nonzero exit code.

## Verified properties

The executable uses the pure `parseName` and `classify` functions in [`Spec.lean`](Spec.lean).
Lean proofs establish that every accepted key resolves to one nonempty relative
component without `.` or `..`, and that the supported JSON forms map to the
intended directory, file, link, or script operation. They also cover rejected
scalar values, empty arrays, and unknown array tags. These proofs do not establish
correctness of filesystem operations, external `ln`/`chmod`, or equivalence to the
Rust implementation for all inputs.

## License

The Lean implementation is licensed under the [WTFPL](LICENSE) (`WTFPL`).
The upstream Rust reference retains its own license in its repository.
