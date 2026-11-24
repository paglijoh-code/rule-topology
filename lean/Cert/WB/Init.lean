import Cert.WB.Wall
import Cert.WB.I00
import Cert.WB.I01
import Cert.WB.I02
import Cert.WB.I03
import Cert.WB.I04
import Cert.WB.I05
import Cert.WB.I06
import Cert.WB.I07
import Cert.WB.I08
import Cert.WB.I09
import Cert.WB.I10
import Cert.WB.I11
import Cert.WB.I12
import Cert.WB.I13
import Cert.WB.I14
import Cert.WB.I15
import Cert.WB.I16
import Cert.WB.I17
import Cert.WB.I18
import Cert.WB.I19
import Cert.WB.I20
import Cert.WB.I21
import Cert.WB.I22
import Cert.WB.I23
import Cert.WB.I24
import Cert.WB.I25
import Cert.WB.I26
import Cert.WB.I27
import Cert.WB.I28
import Cert.WB.I29
import Cert.WB.I30
import Cert.WB.I31
import Cert.WB.I32
import Cert.WB.I33
import Cert.WB.I34
import Cert.WB.I35
import Cert.WB.I36
import Cert.WB.I37
import Cert.WB.I38
import Cert.WB.I39
import Cert.WB.I40
import Cert.WB.I41
import Cert.WB.I42
import Cert.WB.I43
import Cert.WB.I44
import Cert.WB.I45
import Cert.WB.I46
import Cert.WB.I47
import Cert.WB.I48
import Cert.WB.I49
import Cert.WB.I50
import Cert.WB.I51
import Cert.WB.I52
import Cert.WB.I53
import Cert.WB.I54
import Cert.WB.I55
import Cert.WB.I56
import Cert.WB.I57
import Cert.WB.I58
import Cert.WB.I59
import Cert.WB.I60
import Cert.WB.I61
import Cert.WB.I62
import Cert.WB.I63
import Cert.WB.I64
import Cert.WB.I65
import Cert.WB.I66
import Cert.WB.I67
import Cert.WB.I68
import Cert.WB.I69
import Cert.WB.I70
import Cert.WB.I71
namespace Family.Cert.WB
open Family

def endRows : Nat := 1795
def endShape : Shape := I71.s1
def endCnt : List Nat := I71.n1

theorem start_eq : applyMoves (sigma0 gper.length) [] start = some (I00.s0, I00.n0) := by
  decide +kernel

/-- The concrete initial run: the stack after `endRows` rows is `decode endShape endCnt`. -/
theorem initial_run : ∀ x, decode endShape endCnt x = St S1 gpre gper endRows x := by
  have d := start_sound S1 gpre gper start_eq
  have d0 := seg_next S1 gpre gper hS hp I00.ok I00.len
    (by decide +kernel) d
  have d1 := seg_next S1 gpre gper hS hp I01.ok I01.len
    (by decide +kernel) d0
  have d2 := seg_next S1 gpre gper hS hp I02.ok I02.len
    (by decide +kernel) d1
  have d3 := seg_next S1 gpre gper hS hp I03.ok I03.len
    (by decide +kernel) d2
  have d4 := seg_next S1 gpre gper hS hp I04.ok I04.len
    (by decide +kernel) d3
  have d5 := seg_next S1 gpre gper hS hp I05.ok I05.len
    (by decide +kernel) d4
  have d6 := seg_next S1 gpre gper hS hp I06.ok I06.len
    (by decide +kernel) d5
  have d7 := seg_next S1 gpre gper hS hp I07.ok I07.len
    (by decide +kernel) d6
  have d8 := seg_next S1 gpre gper hS hp I08.ok I08.len
    (by decide +kernel) d7
  have d9 := seg_next S1 gpre gper hS hp I09.ok I09.len
    (by decide +kernel) d8
  have d10 := seg_next S1 gpre gper hS hp I10.ok I10.len
    (by decide +kernel) d9
  have d11 := seg_next S1 gpre gper hS hp I11.ok I11.len
    (by decide +kernel) d10
  have d12 := seg_next S1 gpre gper hS hp I12.ok I12.len
    (by decide +kernel) d11
  have d13 := seg_next S1 gpre gper hS hp I13.ok I13.len
    (by decide +kernel) d12
  have d14 := seg_next S1 gpre gper hS hp I14.ok I14.len
    (by decide +kernel) d13
  have d15 := seg_next S1 gpre gper hS hp I15.ok I15.len
    (by decide +kernel) d14
  have d16 := seg_next S1 gpre gper hS hp I16.ok I16.len
    (by decide +kernel) d15
  have d17 := seg_next S1 gpre gper hS hp I17.ok I17.len
    (by decide +kernel) d16
  have d18 := seg_next S1 gpre gper hS hp I18.ok I18.len
    (by decide +kernel) d17
  have d19 := seg_next S1 gpre gper hS hp I19.ok I19.len
    (by decide +kernel) d18
  have d20 := seg_next S1 gpre gper hS hp I20.ok I20.len
    (by decide +kernel) d19
  have d21 := seg_next S1 gpre gper hS hp I21.ok I21.len
    (by decide +kernel) d20
  have d22 := seg_next S1 gpre gper hS hp I22.ok I22.len
    (by decide +kernel) d21
  have d23 := seg_next S1 gpre gper hS hp I23.ok I23.len
    (by decide +kernel) d22
  have d24 := seg_next S1 gpre gper hS hp I24.ok I24.len
    (by decide +kernel) d23
  have d25 := seg_next S1 gpre gper hS hp I25.ok I25.len
    (by decide +kernel) d24
  have d26 := seg_next S1 gpre gper hS hp I26.ok I26.len
    (by decide +kernel) d25
  have d27 := seg_next S1 gpre gper hS hp I27.ok I27.len
    (by decide +kernel) d26
  have d28 := seg_next S1 gpre gper hS hp I28.ok I28.len
    (by decide +kernel) d27
  have d29 := seg_next S1 gpre gper hS hp I29.ok I29.len
    (by decide +kernel) d28
  have d30 := seg_next S1 gpre gper hS hp I30.ok I30.len
    (by decide +kernel) d29
  have d31 := seg_next S1 gpre gper hS hp I31.ok I31.len
    (by decide +kernel) d30
  have d32 := seg_next S1 gpre gper hS hp I32.ok I32.len
    (by decide +kernel) d31
  have d33 := seg_next S1 gpre gper hS hp I33.ok I33.len
    (by decide +kernel) d32
  have d34 := seg_next S1 gpre gper hS hp I34.ok I34.len
    (by decide +kernel) d33
  have d35 := seg_next S1 gpre gper hS hp I35.ok I35.len
    (by decide +kernel) d34
  have d36 := seg_next S1 gpre gper hS hp I36.ok I36.len
    (by decide +kernel) d35
  have d37 := seg_next S1 gpre gper hS hp I37.ok I37.len
    (by decide +kernel) d36
  have d38 := seg_next S1 gpre gper hS hp I38.ok I38.len
    (by decide +kernel) d37
  have d39 := seg_next S1 gpre gper hS hp I39.ok I39.len
    (by decide +kernel) d38
  have d40 := seg_next S1 gpre gper hS hp I40.ok I40.len
    (by decide +kernel) d39
  have d41 := seg_next S1 gpre gper hS hp I41.ok I41.len
    (by decide +kernel) d40
  have d42 := seg_next S1 gpre gper hS hp I42.ok I42.len
    (by decide +kernel) d41
  have d43 := seg_next S1 gpre gper hS hp I43.ok I43.len
    (by decide +kernel) d42
  have d44 := seg_next S1 gpre gper hS hp I44.ok I44.len
    (by decide +kernel) d43
  have d45 := seg_next S1 gpre gper hS hp I45.ok I45.len
    (by decide +kernel) d44
  have d46 := seg_next S1 gpre gper hS hp I46.ok I46.len
    (by decide +kernel) d45
  have d47 := seg_next S1 gpre gper hS hp I47.ok I47.len
    (by decide +kernel) d46
  have d48 := seg_next S1 gpre gper hS hp I48.ok I48.len
    (by decide +kernel) d47
  have d49 := seg_next S1 gpre gper hS hp I49.ok I49.len
    (by decide +kernel) d48
  have d50 := seg_next S1 gpre gper hS hp I50.ok I50.len
    (by decide +kernel) d49
  have d51 := seg_next S1 gpre gper hS hp I51.ok I51.len
    (by decide +kernel) d50
  have d52 := seg_next S1 gpre gper hS hp I52.ok I52.len
    (by decide +kernel) d51
  have d53 := seg_next S1 gpre gper hS hp I53.ok I53.len
    (by decide +kernel) d52
  have d54 := seg_next S1 gpre gper hS hp I54.ok I54.len
    (by decide +kernel) d53
  have d55 := seg_next S1 gpre gper hS hp I55.ok I55.len
    (by decide +kernel) d54
  have d56 := seg_next S1 gpre gper hS hp I56.ok I56.len
    (by decide +kernel) d55
  have d57 := seg_next S1 gpre gper hS hp I57.ok I57.len
    (by decide +kernel) d56
  have d58 := seg_next S1 gpre gper hS hp I58.ok I58.len
    (by decide +kernel) d57
  have d59 := seg_next S1 gpre gper hS hp I59.ok I59.len
    (by decide +kernel) d58
  have d60 := seg_next S1 gpre gper hS hp I60.ok I60.len
    (by decide +kernel) d59
  have d61 := seg_next S1 gpre gper hS hp I61.ok I61.len
    (by decide +kernel) d60
  have d62 := seg_next S1 gpre gper hS hp I62.ok I62.len
    (by decide +kernel) d61
  have d63 := seg_next S1 gpre gper hS hp I63.ok I63.len
    (by decide +kernel) d62
  have d64 := seg_next S1 gpre gper hS hp I64.ok I64.len
    (by decide +kernel) d63
  have d65 := seg_next S1 gpre gper hS hp I65.ok I65.len
    (by decide +kernel) d64
  have d66 := seg_next S1 gpre gper hS hp I66.ok I66.len
    (by decide +kernel) d65
  have d67 := seg_next S1 gpre gper hS hp I67.ok I67.len
    (by decide +kernel) d66
  have d68 := seg_next S1 gpre gper hS hp I68.ok I68.len
    (by decide +kernel) d67
  have d69 := seg_next S1 gpre gper hS hp I69.ok I69.len
    (by decide +kernel) d68
  have d70 := seg_next S1 gpre gper hS hp I70.ok I70.len
    (by decide +kernel) d69
  have d71 := seg_next S1 gpre gper hS hp I71.ok I71.len
    (by decide +kernel) d70
  exact d71

end Family.Cert.WB
