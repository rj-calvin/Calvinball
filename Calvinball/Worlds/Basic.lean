import Calvinball.Forms.Basic
import Calvinball.Frames.Basic
import Calvinball.Trytes.Basic

universe u v

open Form Frame

abbrev WorldFrame (ε : Type v) (α : Type u) := Frame 6 ε (Form 3 ε α)

abbrev MachineLine := StateT Tryte IO TryteLine
abbrev MachineBall := StateCpsT MachineLine BaseIO TryteSlab

def WorldLine := WorldFrame MachineLine (StateT TryteSlab IO (TryteLine × TryteSlab))
def WorldBall := WorldFrame MachineBall (StateT TryteBall IO (TryteLine × TryteSlab))
def WorldBall.mk : WorldBall := obj default

instance : Inhabited WorldLine where default := rel ref
instance : Inhabited WorldBall where default := ref default
