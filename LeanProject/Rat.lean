import LeanProject.Structures
import LeanProject.Nat
import LeanProject.Int

namespace Project

def natEquivalence : Relation (Pair Z Z)
| a, b => a.fst * b.snd = a.snd * b.fst

end Project
