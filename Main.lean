import Spec

open Lean Json2Dir

private abbrev JsonObject := Std.TreeMap.Raw String Json compare

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def checkedName (parent : System.FilePath) (name : String) : IO System.FilePath := do
  match parseName name with
  | .ok part => return parent / part
  | .error .multipleComponents =>
    fail s!"the key {repr name} under {repr parent.toString} must have exactly one path component"
  | .error .nonRegularComponent =>
    fail s!"the key {repr name} under {repr parent.toString} is a non-regular path component"

private def checkedEntry (path : System.FilePath) (value : Json) : IO Entry :=
  match classify value with
  | .ok entry => pure entry
  | .error .invalidArrayKind =>
    fail s!"expected a JSON array's first element to be either \"link\" or \"script\" while at {repr path.toString}"
  | .error .invalidArray =>
    fail s!"expected a JSON array to be of the form [type, payload] while at {repr path.toString}"
  | .error .invalidPart =>
    fail s!"expected a JSON value to be an object, an array, or a string while at {repr path.toString}"

private def create (kind : String) (path : System.FilePath) (action : IO Unit) : IO Unit := do
  try action
  catch e => fail s!"couldn't create a {kind} at {repr path.toString}: {e}"

private def runCommand (errorPrefix command : String) (args : Array String) : IO Unit := do
  let result ← try IO.Process.output { cmd := command, args := args }
    catch e => fail s!"{errorPrefix}: {e}"
  if result.exitCode != 0 then
    fail s!"{errorPrefix}: {result.stderr.trimAscii.toString}"

private def removeOldFile (path : System.FilePath) : IO Unit :=
  -- Remove files and symlinks; ignore missing paths and directories.
  IO.FS.removeFile path <|> pure ()

private def ensureDirectory (path : System.FilePath) : IO Unit := do
  try IO.FS.createDir path
  catch e =>
    match e with
    | .alreadyExists .. => pure ()
    | _ => fail s!"couldn't create a directory at {repr path.toString}: {e}"

  let metadata ← try path.symlinkMetadata
    catch e => fail s!"couldn't inspect directory at {repr path.toString}: {e}"
  if metadata.type != .dir then
    fail s!"expected a directory at {repr path.toString}"

private def createLink (path : System.FilePath) (target : String) : IO Unit := do
  let errorPrefix := s!"couldn't create a symlink at {repr path.toString}"
  if target.contains '\x00' then
    fail s!"{errorPrefix}: target contains NUL"

  -- `ln` would otherwise create the link *inside* an existing directory.
  match (← path.symlinkMetadata.toBaseIO) with
  | .ok metadata =>
    if metadata.type == .dir then
      fail s!"{errorPrefix}: a directory already exists"
  | .error _ => pure ()

  runCommand errorPrefix "ln" #["-s", "--", target, path.toString]

private def createScript (path : System.FilePath) (content : String) : IO Unit := do
  create "script" path (IO.FS.writeFile path content)
  runCommand s!"couldn't make the script executable at {repr path.toString}"
    "chmod" #["a+x", "--", path.toString]

private partial def writeObject (parent : System.FilePath) (entries : JsonObject) : IO Unit := do
  for (name, value) in entries.toList do
    let path ← checkedName parent name
    removeOldFile path
    let entry ← checkedEntry path value
    match entry with
    | .directory children =>
      ensureDirectory path
      writeObject path children
    | .file content => create "regular file" path (IO.FS.writeFile path content)
    | .link target => createLink path target
    | .script content => createScript path content

private def parseInput (input : String) : IO JsonObject := do
  -- Lean's JSON parser substitutes U+FFFD for lone surrogate escapes.
  if !validUnicodeEscapes input then
    fail "couldn't convert stdin to JSON"
  let value ← match Json.parse input with
    | .ok value => pure value
    | .error _ => fail "couldn't convert stdin to JSON"
  match value with
  | .obj entries => pure entries
  | _ => fail "expected provided JSON to be an object"

def main (args : List String) : IO UInt32 := do
  if !args.isEmpty then
    IO.eprintln "Usage: json2dir < file.json"
    return 1
  try
    let input ← (← IO.getStdin).readToEnd
    let entries ← parseInput input
    writeObject "." entries
    return 0
  catch e =>
    IO.eprintln s!"Error: {e}."
    return 1
