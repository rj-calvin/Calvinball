import Calvinball.Forms.Basic
import Calvinball.Frames.Basic
import Calvinball.Trytes.Mech

universe u v w

open Form Frame

def WorldFrameT (ε : Type v) (m : Type u → Type w) (α : Type u) := Frame 6 ε (Form 3 ε (m α))

def WorldLineT := WorldFrameT MechLine BaseIO
def WorldBallT (α : Type) := WorldFrameT (MechBall α) BaseIO α
