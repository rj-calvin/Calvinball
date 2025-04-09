import Calvinball.Worlds.Basic

abbrev Shell (m : Type 2 → Type 3) := StateT WorldLine m WorldLine
abbrev WorldShell (m : Type 3 → Type 3) := StateT WorldBall m WorldBall
