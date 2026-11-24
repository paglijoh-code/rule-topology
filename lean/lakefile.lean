import Lake
open Lake DSL

package ruletopology where

@[default_target] lean_lib LeadADefs
@[default_target] lean_lib LeadACrossData
@[default_target] lean_lib LeadACross
@[default_target] lean_lib LeadACrossThms
@[default_target] lean_lib LeadACheck
@[default_target] lean_lib LeadAData
@[default_target] lean_lib LeadAProof
@[default_target] lean_lib LeadAMut
@[default_target] lean_lib LeadASpec
@[default_target] lean_lib LeadASound
@[default_target] lean_lib LeadAMain
@[default_target] lean_lib SqrtModel
@[default_target] lean_lib SqrtCross
@[default_target] lean_lib SqrtVirt
@[default_target] lean_lib SqrtR
@[default_target] lean_lib SqrtJump
@[default_target] lean_lib SqrtGlue
@[default_target] lean_lib SqrtRound
@[default_target] lean_lib SqrtWin
@[default_target] lean_lib SqrtBig
@[default_target] lean_lib SqrtSmall
@[default_target] lean_lib SqrtSound
@[default_target] lean_lib SqrtPre
@[default_target] lean_lib SqrtMain
@[default_target] lean_lib SqrtCor
@[default_target] lean_lib SqrtFar
@[default_target] lean_lib FamilyJump
@[default_target] lean_lib FamilyRun
@[default_target] lean_lib FamilyGame
@[default_target] lean_lib FamilyStack
@[default_target] lean_lib FamilyBlock
@[default_target] lean_lib FamilyCheck
@[default_target] lean_lib FamilyFast
@[default_target] lean_lib FamilyRound
@[default_target] lean_lib CertWB where
  roots := #[`Cert.WB.Init]
  globs := #[.submodules `Cert.WB]
@[default_target] lean_lib CertWA where
  roots := #[`Cert.WA.Init]
  globs := #[.submodules `Cert.WA]
@[default_target] lean_lib FamilyWall
@[default_target] lean_lib FamilyPhase
@[default_target] lean_lib FamilyMain

/-- All further walls of certificates/walls.csv: not a default target; generate the sources first (README), then build with `lake build CertAll`. -/
lean_lib CertAll where
  roots := #[]
  globs := #[
    .submodules `Cert.Wr10_s1_2_5_6_9_g01234_p0,
    .submodules `Cert.Wr10_s1_4_7_8_9_10_g00112233041520310213_p12,
    .submodules `Cert.Wr10_s1_6_8_9_10_g0001112220331442_p0,
    .submodules `Cert.Wr10_s1_2_4_7_9_10_g0123456_p0,
    .submodules `Cert.Wr10_s1_2_7_9_10_g0123456_p0,
    .submodules `Cert.Wr10_s1_2_4_9_10_g0123456_p0,
    .submodules `Cert.Wr10_s1_2_5_6_9_10_g012345678_p0,
    .submodules `Cert.Wr10_s3_4_9_10_g01234_p0,
    .submodules `Cert.Wr10_s3_4_9_10_g00112233041520314_p12,
    .submodules `Cert.Wr10_s2_3_6_7_10_g0123456_p0,
    .submodules `Cert.Wr10_s1_2_5_6_9_g00112233041520314_p12,
    .submodules `Cert.Wr10_s4_5_6_7_8_9_g00112233041520314_p12,
    .submodules `Cert.Wr10_s1_3_4_6_8_10_g0001112023134002113_p13,
    .submodules `Cert.Wr10_s1_3_4_6_8_10_g0001112023134005114002113_p19,
    .submodules `Cert.Wr10_s4_5_6_7_8_9_g01234_p0,
    .submodules `Cert.Wr10_s4_5_6_8_9_g00112233041520314_p12,
    .submodules `Cert.Wp7_12_s1_2_3_6_8_g0102211_p0,
    .submodules `Cert.Wr10_s4_5_6_8_9_g01234_p0,
    .submodules `Cert.Wp78_rand_s4_5_6_7_8_10_g01000022_p0,
    .submodules `Cert.Ws1_2_5_6_12_g01234_p0,
    .submodules `Cert.Wr10_s4_5_7_8_9_g00112233041520314_p12,
    .submodules `Cert.Ws1_2_5_6_9_12_g01234_p0,
    .submodules `Cert.Wr10_s1_4_6_8_g0011223340516203142536_p0,
    .submodules `Cert.Ws1_2_3_5_6_8_9_10_12_g01234_p0,
    .submodules `Cert.Wr10_s5_6_7_9_g001122330410213203_p10,
    .submodules `Cert.Ws2_4_10_12_g01234_p0,
    .submodules `Cert.Wr10_s5_6_7_9_g00112233041520310213_p12,
    .submodules `Cert.Wr10_s5_6_7_9_g0011223340510213203_p11,
    .submodules `Cert.Ws1_2_9_11_g0123456_p0,
    .submodules `Cert.Ws1_2_4_9_10_12_g0123456_p0,
    .submodules `Cert.Ws1_2_7_9_10_12_g0123456_p0,
    .submodules `Cert.Ws1_2_4_7_9_10_12_g0123456_p0,
    .submodules `Cert.Wr10_s1_2_5_9_g012345678_p0,
    .submodules `Cert.Ws2_3_6_7_10_11_g0123456_p0,
    .submodules `Cert.Ws2_3_4_10_12_g0123456789_p0,
    .submodules `Cert.Ws2_3_4_9_11_g012345678_p0,
    .submodules `Cert.Ws2_4_9_10_11_g012345678_p0,
    .submodules `Cert.Ws2_3_4_9_10_11_g012345678_p0,
    .submodules `Cert.Ws2_5_8_11_g012345678_p0,
    .submodules `Cert.Ws1_4_9_12_g012345678910_p0,
    .submodules `Cert.Ws1_2_11_12_g012345678910_p0,
    .submodules `Cert.Ws1_2_5_11_12_g012345678910_p0,
    .submodules `Cert.Ws1_2_8_11_12_g012345678910_p0,
    .submodules `Cert.Ws1_2_5_8_11_12_g012345678910_p0]
