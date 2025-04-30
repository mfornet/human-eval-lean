import Lean.Data.Json.FromToJson
import Lean.Data.Json.Parser

namespace HumanEvalLean.CreateScaffold

structure Task where
  task_id : String
  prompt : String
  entry_point : String
  canonical_solution : String
  test : String
deriving Repr, Lean.FromJson

def Task.num? (t : Task) : Option Nat :=
  t.task_id.dropPrefix? "HumanEval/" |>.map (·.toString) |>.bind String.toNat?

instance : ToString Task where
  toString t := repr t |>.pretty

def readFile (filename : System.FilePath) : IO (List Task) := do
  let lines := (← IO.FS.readFile filename).splitOn "\n" |>.filter (fun l => !l.isEmpty)
  lines.mapM fun line => IO.ofExcept (Lean.Json.parse line >>= Lean.FromJson.fromJson?)

def createScaffoldForTask (t : Task) : IO Unit := do
  let some num := t.num? | throw (IO.userError "ill-formed task id")
  let fileName := s!"HumanEvalLean/HumanEval{num}.lean"
  let content := s!"def {t.entry_point} : Unit :=\n  ()\n\n/-!\n## Prompt\n\n```python3\n{t.prompt}```\n\n## Canonical solution\n\n```python3\n{t.canonical_solution}```\n\n## Tests\n\n```python3\n{t.test}```\n-/"
  IO.FS.writeFile fileName content

def createScaffold (filename : String) : IO Unit := do
  let tasks ← HumanEvalLean.CreateScaffold.readFile filename
  tasks.forM createScaffoldForTask

end HumanEvalLean.CreateScaffold

def main (args : List String) : IO Unit := do
  if let [filename] := args then do
    HumanEvalLean.CreateScaffold.createScaffold filename
  else
    IO.println "Expected exactly one argument with a filename"
