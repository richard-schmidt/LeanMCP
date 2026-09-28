# lean-mcp

An MCP server that lets an agent work Lean proofs against the real Lean 4 + Mathlib
checker, on-device in Termux. Stdlib-only Python.

| Tool | What it's for |
|---|---|
| `lean_check` | Errors, warnings, and `sorry`s for a file, plus goal states at chosen lines. `text` checks an unsaved version. |
| `lean_try` | Try several tactics at one line (usually a `sorry`) and get a verdict for each: NO GOALS, PROGRESS, or ERROR. |
| `lean_search` | Offline lemma search by name fragments, over everything in scope for a file. |
| `lean_build` | `lake build` of the whole project, as a final gate. |

**No MCP tool writes files.** The agent edits with its own tools and checks with these.

## Bridge (for the Lean Workbench app)

`bridge.py` serves the same Session over `127.0.0.1:8766` to the app
(`~/AndroidProjects/LeanWorkbench`). HTTP and auth only; every decision is in `core.py`.

| Endpoint | Returns / does |
|---|---|
| `GET /v1/health` | `{ok, project}`; no token needed |
| `GET /v1/files` | the project's `.lean` paths |
| `GET /v1/overview` | per source: title, declaration and `sorry` counts, role (root / imported / unimported / other); no Lean run |
| `POST /v1/check {file, text?, goals_at?, goals_after?}` | diagnostics, declarations with status, parsed goals before/after lines, and `tokens`: Lean's semantic tokens `[line, col, length, kind]` (1-based lines, UTF-16 columns; keyword / variable / property / function / sorry) |
| `POST /v1/complete {file, text, line, col}` | Lean's completions, filtered and ranked (locals first, at most 20) |
| `POST /v1/save {file, text, base}` | overwrites an existing source if the disk still equals `base` |
| `POST /v1/create {file, text}` | a new source in a library folder; adds its import to the library root |
| `GET /v1/abbreviations`, `POST /v1/abbreviation {name, symbol}` | the project's `\`-abbreviations |
| `POST /v1/search {engine, query, file?, text?}` | Loogle or LeanSearch hits, each `ok` / `import` / `missing` in the file's scope; a bad Loogle query gives `error` + `suggestions` (~35 s cold, 2-3 s warm) |
| `GET /v1/toolbox`, `POST /v1/toolbox {name, module, type, pinned}` | the package's pinned lemmas |
| `POST /v1/source {module, name?}` | a module's source, read-only, with the declaration's line |
| `GET /v1/packages` | every Lake package under `LEAN_PACKAGES` (default: the project's parent): libraries with file overviews, loose sources, git, last CI run (`gh`, cached 2 min), dependencies |
| `POST /v1/library {name}` | a new `[[lean_lib]]` in `lakefile.toml` (also a default target) and its root `<name>.lean` |

Every endpoint but `health` and `packages` acts on the package in the `X-Lean-Package` header (default: the
project); each package gets its own Lean server, started on first use, stopped when idle.

**Auth:** `Authorization: Bearer <token>` on everything but health. Any app can reach
127.0.0.1 and `#eval` runs code, so the token (`~/.config/lean-bridge/token`, mode 600) is the
guard. `bridge.py --pair` sends it to the app by deep link.

**Writes:** checks never write; edits travel as `text`. Nothing commits (git is the undo).
- `save`: an existing, listed source only, if unchanged since loaded; atomic, mode kept.
- `create`: a new file only (`xb`), capitalised module names, plus its import in the library root.
- `abbreviation`, `toolbox`: only `.leanwb/abbreviations.json`, `.leanwb/toolbox.json`.
- `library`: only `lakefile.toml` (replaced if unchanged since read; `lakefile.lean` refused)
  and a new `<name>.lean`.
- `search` sends only the query off the device; `source` reads only inside the project.

**Starting:** `start-bridge.sh [--detach] [--pair]` starts the bridge unless `/v1/health`
answers, with the Lean PATH set, logging to `$TMPDIR/bridge.log`. The app runs it through
Termux `RUN_COMMAND` in the foreground; `--detach` returns at once.

## Layout

```
leanmcp/core.py     every decision: paths, splicing, UTF-16 columns, verdicts,
                    search snippet + parser, build-output parser, rendering  (unit-tested)
leanmcp/lsp.py      `lake serve` process + LSP framing, Termux env (TZ, shims)
leanmcp/session.py  warm server: open-document LRU (2), dependency-edit reopen,
                    idle shutdown (15 min), restart on death
leanmcp/cli.py      thin CLI (python3 -m leanmcp.cli check|try|search|build)
mcp_server.py       JSON-RPC only; runs the Session in-process so it stays warm
bridge.py           HTTP only, for the app; its own Session in its own process
start-bridge.sh     idempotent start (the app's RUN_COMMAND target)
```

**Stateless contract:** every call carries the full text it's about, or reads it
from disk at call time. The warm Lean server is only a cache. If it dies, the
next call starts a new one.

## Tests

```
./test.sh                 # unit tests (core.py, incl. bridge payloads), instant
./test.sh --integration   # + real Lean: live checks, tries, search, build,
                          #   dependency-edit reopen, JSON-RPC round trip,
                          #   bridge over HTTP (a few minutes)
```

The integration tests need only a Lean toolchain: they run against a small Lake
package in `tests/project/`, copied to a temporary folder for each run, so nothing
in the repo is written.

The tests that need Mathlib (Finset goals, `exact?` over Mathlib, constant search,
Mathlib sources, dependencies) run only when two variables are set, and are skipped
otherwise:

```
LEAN_MATHLIB_PROJECT=~/path/to/a/package/with/mathlib/built \
LEAN_MATHLIB_FILE=Some/File.lean \
./test.sh --integration
```

`LEAN_MATHLIB_FILE` must import `Mathlib.Data.Finset.Basic`. These tests only pass
text in memory, and fail if the package's `git status` changes.

## Registration

```
claude mcp add --scope user lean -- python3 ~/LeanProjects/lean-mcp/mcp_server.py
```

`LEAN_PROJECT` sets the default project (default: `~/LeanProjects/synthetic-systems`).
An absolute file path finds its own project by walking up to the nearest lakefile.
Restart Claude Code after registering.

## Termux prerequisites

Lean's official aarch64 binaries target glibc, and elan cannot download them on
Android (it cannot resolve DNS there). `termux/termux-lean-toolchain.sh <tag>`
installs a toolchain into elan instead: it downloads the release with Termux's
`curl`, points every binary at Termux's glibc loader, wraps `ld.lld` so executables
Lake links get the same loader, writes `curl`/`git` shims to
`~/.elan/termux-shims` (put it on `PATH`), and unpacks timezone files to
`~/.local/share/zoneinfo`.

```
pkg install glibc-runner patchelf zstd binutils curl git python unzip
bash termux/termux-lean-toolchain.sh v4.35.0-rc2     # the tag from lean-toolchain
bash termux/termux-lean-toolchain.sh --repatch v4.35.0-rc2   # after an update
```

elan itself must be installed first; the script only replaces
`elan toolchain install`.

## Lean behaviours the server depends on

- **`lake serve` needs a timezone.** Android has no `/etc/localtime`, and Lean accepts only
  `TZ=<absolute path to a TZif file>`. `lsp.lean_env()` sets it for Lean processes only.
- **Lean 4.35 writes ``declaration uses `sorry` ``** (backticks). `core.uses_sorry` matches
  both this and the older `'sorry'` form.
- **An open document does not see edits to its imports.** Lean sends no "imports out of date"
  message; it reports a false "unknown identifier". The session snapshots source mtimes and
  reopens the document when another source file changed (`DependencyEdit` test).

## License

Copyright (C) 2026 Richard Schmidt.

- **Code** is licensed under the GNU Affero General Public License, version 3 or
  any later version: see [LICENSE](LICENSE). If you run a modified version as a
  service others use over a network, you must offer them its source.
- **Documentation** (this README) is licensed under Creative Commons
  Attribution 4.0 International: see [LICENSE-CONTENT](LICENSE-CONTENT).
