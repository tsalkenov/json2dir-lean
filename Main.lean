import Spec

open Lean
open Json2Dir

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def checkedName (name : String) (parent : System.FilePath) : IO System.FilePath := do
  match parseName name with
  | .ok part => return parent / part
  | .error .multipleComponents =>
    fail s!"the key {repr name} under {repr parent.toString} must have exactly one path component"
  | .error .nonRegularComponent =>
    fail s!"the key {repr name} under {repr parent.toString} is a non-regular path component"

private def create (kind : String) (path : System.FilePath) (action : IO Unit) : IO Unit := do
  try action
  catch e => fail s!"couldn't create a {kind} at {repr path.toString}: {e}"

private def runCommand (kind : String) (path : System.FilePath)
    (command : String) (args : Array String) : IO Unit := do
  let result ← try IO.Process.output { cmd := command, args := args }
    catch e => fail s!"couldn't create a {kind} at {repr path.toString}: {e}"
  if result.exitCode != 0 then
    fail s!"couldn't create a {kind} at {repr path.toString}: {result.stderr.trimAscii.toString}"

private partial def writeObject (parent : System.FilePath)
    (entries : Std.TreeMap.Raw String Json compare) : IO Unit := do
  for (name, value) in entries.toList do
    let path ← checkedName name parent
    -- Removing a file also removes a pre-existing symlink, including a dangling one.
    try IO.FS.removeFile path catch _ => pure ()
    match classify value with
    | .ok (.directory children) =>
      try IO.FS.createDir path
      catch e =>
        match e with
        | .alreadyExists .. => pure ()
        | _ => fail s!"couldn't create a directory at {repr path.toString}: {e}"
      let metadata ← try path.symlinkMetadata
        catch e => fail s!"couldn't set the current dir to the newly created path {repr path.toString}: {e}"
      if metadata.type != .dir then
        fail s!"couldn't set the current dir to the newly created path {repr path.toString}: not a directory"
      writeObject path children
    | .ok (.file content) =>
      create "regular file" path (IO.FS.writeFile path content)
    | .ok (.link target) =>
      runCommand "symlink" path "ln" #["-s", "--", target, path.toString]
    | .ok (.script content) =>
      create "script" path (IO.FS.writeFile path content)
      let result ← try IO.Process.output { cmd := "chmod", args := #["a+x", "--", path.toString] }
        catch e => fail s!"couldn't make the script executable at {repr path.toString}: {e}"
      if result.exitCode != 0 then
        fail s!"couldn't make the script executable at {repr path.toString}: {result.stderr.trimAscii.toString}"
    | .error .invalidArrayKind =>
      fail s!"expected a JSON array's first element to be either \"link\" or \"script\" while at {repr path.toString}"
    | .error .invalidArray =>
      fail s!"expected a JSON array to be of the form [type, payload] while at {repr path.toString}"
    | .error .invalidPart =>
      fail s!"expected a JSON value to be an object, an array, or a string while at {repr path.toString}"

def main (args : List String) : IO UInt32 := do
  if !args.isEmpty then
    IO.eprintln "Usage: json2dir < file.json"
    return 1
  try
    let input ← IO.getStdin >>= (·.readToEnd)
    let json ← match Json.parse input with
      | .ok value => pure value
      | .error _ => fail "couldn't convert stdin to JSON"
    match json with
    | .obj entries => writeObject "." entries
    | _ => fail "expected provided JSON to be an object"
    return 0
  catch e =>
    IO.eprintln s!"Error: {e}."
    return 1
