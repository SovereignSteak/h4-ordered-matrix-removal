import H4Formal.Host

/-!
# Generated ground host-oracle regression checks

Deterministic finite cell-value comparisons with the bundled Python model.
Each expected Boolean equality is checked by the Lean kernel.
-/

namespace H4Formal

theorem ground_0000 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0001 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0002 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0003 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0004 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0005 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0006 :
    hostValue 1 Block.dummy (Block.variable 1 0 Sign.leaf) = true := by
  decide

theorem ground_0007 :
    repairedValue 1 Block.dummy (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0008 :
    hostValue 1 Block.dummy Block.dummy = true := by
  decide

theorem ground_0009 :
    repairedValue 1 Block.dummy Block.dummy = true := by
  decide

theorem ground_0010 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0011 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0012 :
    hostValue 1 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0013 :
    repairedValue 1 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0014 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0015 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0016 :
    hostValue 1 (Block.variable 0 0 Sign.plus) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0017 :
    repairedValue 1 (Block.variable 0 0 Sign.plus) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0018 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0019 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0020 :
    hostValue 1 (Block.variable 1 1 Sign.leaf) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0021 :
    repairedValue 1 (Block.variable 1 1 Sign.leaf) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0022 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0023 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0024 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0025 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0026 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0027 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0028 :
    hostValue 1 (Block.variable 0 0 Sign.minus) Block.dummy = true := by
  decide

theorem ground_0029 :
    repairedValue 1 (Block.variable 0 0 Sign.minus) Block.dummy = true := by
  decide

theorem ground_0030 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) Block.dummy = false := by
  decide

theorem ground_0031 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) Block.dummy = false := by
  decide

theorem ground_0032 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0033 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0034 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0035 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0036 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0037 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0038 :
    hostValue 1 (Block.variable 0 0 Sign.plus) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0039 :
    repairedValue 1 (Block.variable 0 0 Sign.plus) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0040 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0041 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0042 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0043 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0044 :
    hostValue 1 (Block.variable 0 0 Sign.minus) (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0045 :
    repairedValue 1 (Block.variable 0 0 Sign.minus) (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0046 :
    hostValue 1 (Block.variable 1 1 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0047 :
    repairedValue 1 (Block.variable 1 1 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0048 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0049 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0050 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0051 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0052 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0053 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0054 :
    hostValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0055 :
    repairedValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0056 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.variable 0 0 Sign.plus) = true := by
  decide

theorem ground_0057 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.variable 0 0 Sign.plus) = true := by
  decide

theorem ground_0058 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0059 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0060 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0061 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0062 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0063 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0064 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0065 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0066 :
    hostValue 1 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0067 :
    repairedValue 1 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0068 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) Block.dummy = false := by
  decide

theorem ground_0069 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) Block.dummy = false := by
  decide

theorem ground_0070 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) Block.dummy = false := by
  decide

theorem ground_0071 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) Block.dummy = false := by
  decide

theorem ground_0072 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0073 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0074 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0075 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0076 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0077 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0078 :
    hostValue 1 (Block.variable 1 1 Sign.leaf) (Block.variable 1 1 Sign.leaf) = true := by
  decide

theorem ground_0079 :
    repairedValue 1 (Block.variable 1 1 Sign.leaf) (Block.variable 1 1 Sign.leaf) = true := by
  decide

theorem ground_0080 :
    hostValue 1 (Block.variable 1 1 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0081 :
    repairedValue 1 (Block.variable 1 1 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0082 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0083 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.leaf) = false := by
  decide

theorem ground_0084 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0085 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0086 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.variable 1 0 Sign.leaf) = true := by
  decide

theorem ground_0087 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.variable 1 0 Sign.leaf) = true := by
  decide

theorem ground_0088 :
    hostValue 1 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0089 :
    repairedValue 1 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0090 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0091 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0092 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0093 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0094 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0095 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0096 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0097 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0098 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0099 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0100 :
    hostValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0101 :
    repairedValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0102 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0103 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0104 :
    hostValue 1 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0105 :
    repairedValue 1 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0106 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0107 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0108 :
    hostValue 1 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = true := by
  decide

theorem ground_0109 :
    repairedValue 1 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = true := by
  decide

theorem ground_0110 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0111 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0112 :
    hostValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0113 :
    repairedValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0114 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0115 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0116 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0117 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0118 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.minus) = true := by
  decide

theorem ground_0119 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.minus) = true := by
  decide

theorem ground_0120 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0121 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0122 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 1 1 Sign.leaf) = false := by
  decide

theorem ground_0123 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 1 1 Sign.leaf) = false := by
  decide

theorem ground_0124 :
    hostValue 1 (Block.variable 0 0 Sign.plus) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0125 :
    repairedValue 1 (Block.variable 0 0 Sign.plus) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0126 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) Block.dummy = true := by
  decide

theorem ground_0127 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) Block.dummy = true := by
  decide

theorem ground_0128 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0129 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0130 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0131 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0132 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0133 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0134 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0135 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0136 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0137 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0138 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0139 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0140 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0141 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0142 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0143 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0144 :
    hostValue 1 (Block.variable 1 1 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0145 :
    repairedValue 1 (Block.variable 1 1 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0146 :
    hostValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0147 :
    repairedValue 1 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0148 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.variable 1 0 Sign.leaf) = true := by
  decide

theorem ground_0149 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.variable 1 0 Sign.leaf) = true := by
  decide

theorem ground_0150 :
    hostValue 1 Block.dummy (Block.variable 1 1 Sign.leaf) = true := by
  decide

theorem ground_0151 :
    repairedValue 1 Block.dummy (Block.variable 1 1 Sign.leaf) = false := by
  decide

theorem ground_0152 :
    hostValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0153 :
    repairedValue 1 (Block.variable 1 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0154 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0155 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0156 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0157 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0158 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0159 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0160 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0161 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0162 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0163 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0164 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0165 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0166 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0167 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0168 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0169 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0170 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0171 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0172 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0173 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0174 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0175 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0176 :
    hostValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0177 :
    repairedValue 1 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0178 :
    hostValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0179 :
    repairedValue 1 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0180 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0181 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0182 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0183 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0184 :
    hostValue 2 (Block.variable 2 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0185 :
    repairedValue 2 (Block.variable 2 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0186 :
    hostValue 2 Block.dummy (Block.variable 2 0 Sign.leaf) = true := by
  decide

theorem ground_0187 :
    repairedValue 2 Block.dummy (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0188 :
    hostValue 2 Block.dummy Block.dummy = true := by
  decide

theorem ground_0189 :
    repairedValue 2 Block.dummy Block.dummy = true := by
  decide

theorem ground_0190 :
    hostValue 2 (Block.variable 2 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0191 :
    repairedValue 2 (Block.variable 2 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0192 :
    hostValue 2 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0193 :
    repairedValue 2 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0194 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0195 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0196 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0197 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0198 :
    hostValue 2 (Block.variable 2 3 Sign.leaf) (Block.variable 1 1 Sign.plus) = true := by
  decide

theorem ground_0199 :
    repairedValue 2 (Block.variable 2 3 Sign.leaf) (Block.variable 1 1 Sign.plus) = true := by
  decide

theorem ground_0200 :
    hostValue 2 (Block.variable 2 2 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0201 :
    repairedValue 2 (Block.variable 2 2 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0202 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0203 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0204 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 1 1 Sign.plus) = false := by
  decide

theorem ground_0205 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 1 1 Sign.plus) = false := by
  decide

theorem ground_0206 :
    hostValue 2 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0207 :
    repairedValue 2 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0208 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0209 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0210 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0211 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0212 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0213 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0214 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0215 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0216 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0217 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0218 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0219 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0220 :
    hostValue 2 (Block.variable 1 0 Sign.plus) (Block.variable 1 1 Sign.plus) = true := by
  decide

theorem ground_0221 :
    repairedValue 2 (Block.variable 1 0 Sign.plus) (Block.variable 1 1 Sign.plus) = true := by
  decide

theorem ground_0222 :
    hostValue 2 (Block.variable 2 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0223 :
    repairedValue 2 (Block.variable 2 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0224 :
    hostValue 2 (Block.variable 2 3 Sign.leaf) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0225 :
    repairedValue 2 (Block.variable 2 3 Sign.leaf) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0226 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 2 3 Sign.leaf) = false := by
  decide

theorem ground_0227 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 2 3 Sign.leaf) = false := by
  decide

theorem ground_0228 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0229 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0230 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0231 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0232 :
    hostValue 2 Block.dummy (Block.variable 2 0 Sign.leaf) = true := by
  decide

theorem ground_0233 :
    repairedValue 2 Block.dummy (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0234 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0235 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0236 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0237 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0238 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 2 3 Sign.leaf) = false := by
  decide

theorem ground_0239 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 2 3 Sign.leaf) = false := by
  decide

theorem ground_0240 :
    hostValue 2 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0241 :
    repairedValue 2 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0242 :
    hostValue 2 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0243 :
    repairedValue 2 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0244 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0245 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0246 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0247 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0248 :
    hostValue 2 (Block.variable 2 2 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0249 :
    repairedValue 2 (Block.variable 2 2 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0250 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0251 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0252 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0253 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0254 :
    hostValue 2 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0255 :
    repairedValue 2 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0256 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0257 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0258 :
    hostValue 2 Block.dummy (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0259 :
    repairedValue 2 Block.dummy (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0260 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0261 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0262 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0263 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0264 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0265 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0266 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0267 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0268 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0269 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0270 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0271 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0272 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0273 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0274 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0275 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0276 :
    hostValue 2 (Block.variable 1 0 Sign.minus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0277 :
    repairedValue 2 (Block.variable 1 0 Sign.minus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0278 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = true := by
  decide

theorem ground_0279 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = true := by
  decide

theorem ground_0280 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0281 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0282 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0283 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0284 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0285 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 2 0 Sign.leaf) = false := by
  decide

theorem ground_0286 :
    hostValue 2 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0287 :
    repairedValue 2 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0288 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0289 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0290 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0291 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0292 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0293 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0294 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0295 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0296 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0297 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0298 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0299 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0300 :
    hostValue 2 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0301 :
    repairedValue 2 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0302 :
    hostValue 2 (Block.variable 2 0 Sign.leaf) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0303 :
    repairedValue 2 (Block.variable 2 0 Sign.leaf) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0304 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0305 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0306 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0307 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0308 :
    hostValue 2 Block.dummy (Block.variable 1 0 Sign.plus) = true := by
  decide

theorem ground_0309 :
    repairedValue 2 Block.dummy (Block.variable 1 0 Sign.plus) = true := by
  decide

theorem ground_0310 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0311 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0312 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) Block.dummy = false := by
  decide

theorem ground_0313 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) Block.dummy = false := by
  decide

theorem ground_0314 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0315 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0316 :
    hostValue 2 (Block.variable 2 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0317 :
    repairedValue 2 (Block.variable 2 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0318 :
    hostValue 2 (Block.variable 1 1 Sign.plus) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0319 :
    repairedValue 2 (Block.variable 1 1 Sign.plus) (Block.variable 2 1 Sign.leaf) = false := by
  decide

theorem ground_0320 :
    hostValue 2 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0321 :
    repairedValue 2 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0322 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0323 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0324 :
    hostValue 2 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0325 :
    repairedValue 2 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0326 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0327 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0328 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0329 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0330 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0331 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0332 :
    hostValue 2 (Block.variable 1 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0333 :
    repairedValue 2 (Block.variable 1 0 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0334 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0335 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0336 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0337 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0338 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0339 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0340 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0341 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0342 :
    hostValue 2 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0343 :
    repairedValue 2 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0344 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0345 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0346 :
    hostValue 2 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0347 :
    repairedValue 2 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0348 :
    hostValue 2 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0349 :
    repairedValue 2 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0350 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0351 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0352 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0353 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0354 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0355 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0356 :
    hostValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) Block.dummy = false := by
  decide

theorem ground_0357 :
    repairedValue 2 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) Block.dummy = false := by
  decide

theorem ground_0358 :
    hostValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0359 :
    repairedValue 2 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0360 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0361 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0362 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 3 0 Sign.leaf) = false := by
  decide

theorem ground_0363 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 3 0 Sign.leaf) = false := by
  decide

theorem ground_0364 :
    hostValue 3 (Block.variable 3 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0365 :
    repairedValue 3 (Block.variable 3 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0366 :
    hostValue 3 Block.dummy (Block.variable 3 0 Sign.leaf) = true := by
  decide

theorem ground_0367 :
    repairedValue 3 Block.dummy (Block.variable 3 0 Sign.leaf) = false := by
  decide

theorem ground_0368 :
    hostValue 3 Block.dummy Block.dummy = true := by
  decide

theorem ground_0369 :
    repairedValue 3 Block.dummy Block.dummy = true := by
  decide

theorem ground_0370 :
    hostValue 3 (Block.variable 3 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0371 :
    repairedValue 3 (Block.variable 3 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0372 :
    hostValue 3 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0373 :
    repairedValue 3 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0374 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0375 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0376 :
    hostValue 3 (Block.variable 0 0 Sign.minus) (Block.variable 1 1 Sign.plus) = false := by
  decide

theorem ground_0377 :
    repairedValue 3 (Block.variable 0 0 Sign.minus) (Block.variable 1 1 Sign.plus) = false := by
  decide

theorem ground_0378 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0379 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0380 :
    hostValue 3 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0381 :
    repairedValue 3 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0382 :
    hostValue 3 (Block.variable 2 3 Sign.plus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0383 :
    repairedValue 3 (Block.variable 2 3 Sign.plus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0384 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0385 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0386 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0387 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0388 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.variable 1 0 Sign.minus) = true := by
  decide

theorem ground_0389 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.variable 1 0 Sign.minus) = true := by
  decide

theorem ground_0390 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0391 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0392 :
    hostValue 3 (Block.variable 1 1 Sign.minus) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0393 :
    repairedValue 3 (Block.variable 1 1 Sign.minus) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0394 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0395 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0396 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0397 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0398 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0399 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0400 :
    hostValue 3 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0401 :
    repairedValue 3 Block.dummy (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0402 :
    hostValue 3 (Block.variable 1 0 Sign.plus) (Block.variable 3 3 Sign.leaf) = false := by
  decide

theorem ground_0403 :
    repairedValue 3 (Block.variable 1 0 Sign.plus) (Block.variable 3 3 Sign.leaf) = false := by
  decide

theorem ground_0404 :
    hostValue 3 (Block.variable 2 3 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0405 :
    repairedValue 3 (Block.variable 2 3 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0406 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0407 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0408 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0409 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0410 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0411 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0412 :
    hostValue 3 (Block.variable 2 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0413 :
    repairedValue 3 (Block.variable 2 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0414 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0415 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0416 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.variable 2 3 Sign.minus) = false := by
  decide

theorem ground_0417 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.variable 2 3 Sign.minus) = false := by
  decide

theorem ground_0418 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0419 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0420 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0421 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0422 :
    hostValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0423 :
    repairedValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0424 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0425 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0426 :
    hostValue 3 (Block.variable 3 1 Sign.leaf) (Block.variable 3 3 Sign.leaf) = true := by
  decide

theorem ground_0427 :
    repairedValue 3 (Block.variable 3 1 Sign.leaf) (Block.variable 3 3 Sign.leaf) = true := by
  decide

theorem ground_0428 :
    hostValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0429 :
    repairedValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0430 :
    hostValue 3 (Block.variable 2 0 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0431 :
    repairedValue 3 (Block.variable 2 0 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0432 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.variable 2 1 Sign.plus) = false := by
  decide

theorem ground_0433 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.variable 2 1 Sign.plus) = false := by
  decide

theorem ground_0434 :
    hostValue 3 (Block.variable 3 4 Sign.leaf) (Block.variable 2 3 Sign.plus) = true := by
  decide

theorem ground_0435 :
    repairedValue 3 (Block.variable 3 4 Sign.leaf) (Block.variable 2 3 Sign.plus) = true := by
  decide

theorem ground_0436 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0437 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0438 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0439 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0440 :
    hostValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0441 :
    repairedValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0442 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0443 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0444 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0445 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0446 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0447 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0448 :
    hostValue 3 (Block.variable 2 2 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0449 :
    repairedValue 3 (Block.variable 2 2 Sign.minus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0450 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0451 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0452 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0453 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0454 :
    hostValue 3 (Block.variable 3 0 Sign.leaf) (Block.variable 1 1 Sign.plus) = false := by
  decide

theorem ground_0455 :
    repairedValue 3 (Block.variable 3 0 Sign.leaf) (Block.variable 1 1 Sign.plus) = false := by
  decide

theorem ground_0456 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0457 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0458 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0459 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0460 :
    hostValue 3 (Block.variable 3 0 Sign.leaf) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0461 :
    repairedValue 3 (Block.variable 3 0 Sign.leaf) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0462 :
    hostValue 3 (Block.variable 3 7 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0463 :
    repairedValue 3 (Block.variable 3 7 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0464 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0465 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.variable 0 0 Sign.minus) = false := by
  decide

theorem ground_0466 :
    hostValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0467 :
    repairedValue 3 (Block.variable 2 2 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0468 :
    hostValue 3 (Block.variable 3 3 Sign.leaf) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0469 :
    repairedValue 3 (Block.variable 3 3 Sign.leaf) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0470 :
    hostValue 3 (Block.variable 3 0 Sign.leaf) (Block.variable 3 5 Sign.leaf) = true := by
  decide

theorem ground_0471 :
    repairedValue 3 (Block.variable 3 0 Sign.leaf) (Block.variable 3 5 Sign.leaf) = true := by
  decide

theorem ground_0472 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0473 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0474 :
    hostValue 3 (Block.variable 2 2 Sign.plus) (Block.variable 3 6 Sign.leaf) = false := by
  decide

theorem ground_0475 :
    repairedValue 3 (Block.variable 2 2 Sign.plus) (Block.variable 3 6 Sign.leaf) = false := by
  decide

theorem ground_0476 :
    hostValue 3 (Block.variable 3 5 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0477 :
    repairedValue 3 (Block.variable 3 5 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0478 :
    hostValue 3 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0479 :
    repairedValue 3 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0480 :
    hostValue 3 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0481 :
    repairedValue 3 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0482 :
    hostValue 3 (Block.variable 2 1 Sign.minus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0483 :
    repairedValue 3 (Block.variable 2 1 Sign.minus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0484 :
    hostValue 3 (Block.variable 3 1 Sign.leaf) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0485 :
    repairedValue 3 (Block.variable 3 1 Sign.leaf) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0486 :
    hostValue 3 (Block.variable 0 0 Sign.minus) (Block.variable 3 4 Sign.leaf) = false := by
  decide

theorem ground_0487 :
    repairedValue 3 (Block.variable 0 0 Sign.minus) (Block.variable 3 4 Sign.leaf) = false := by
  decide

theorem ground_0488 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.variable 3 2 Sign.leaf) = false := by
  decide

theorem ground_0489 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.variable 3 2 Sign.leaf) = false := by
  decide

theorem ground_0490 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0491 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0492 :
    hostValue 3 (Block.variable 3 7 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0493 :
    repairedValue 3 (Block.variable 3 7 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0494 :
    hostValue 3 (Block.variable 1 0 Sign.minus) (Block.variable 2 0 Sign.minus) = false := by
  decide

theorem ground_0495 :
    repairedValue 3 (Block.variable 1 0 Sign.minus) (Block.variable 2 0 Sign.minus) = false := by
  decide

theorem ground_0496 :
    hostValue 3 (Block.variable 2 0 Sign.plus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0497 :
    repairedValue 3 (Block.variable 2 0 Sign.plus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0498 :
    hostValue 3 (Block.variable 3 7 Sign.leaf) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0499 :
    repairedValue 3 (Block.variable 3 7 Sign.leaf) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0500 :
    hostValue 3 (Block.variable 1 0 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0501 :
    repairedValue 3 (Block.variable 1 0 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0502 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0503 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0504 :
    hostValue 3 (Block.variable 2 3 Sign.plus) (Block.variable 3 7 Sign.leaf) = false := by
  decide

theorem ground_0505 :
    repairedValue 3 (Block.variable 2 3 Sign.plus) (Block.variable 3 7 Sign.leaf) = false := by
  decide

theorem ground_0506 :
    hostValue 3 (Block.variable 2 1 Sign.plus) (Block.variable 2 1 Sign.plus) = true := by
  decide

theorem ground_0507 :
    repairedValue 3 (Block.variable 2 1 Sign.plus) (Block.variable 2 1 Sign.plus) = true := by
  decide

theorem ground_0508 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0509 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0510 :
    hostValue 3 (Block.variable 2 1 Sign.minus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0511 :
    repairedValue 3 (Block.variable 2 1 Sign.minus) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0512 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 3 6 Sign.leaf) = false := by
  decide

theorem ground_0513 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 3 6 Sign.leaf) = false := by
  decide

theorem ground_0514 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0515 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0516 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 3 0 Sign.leaf) = false := by
  decide

theorem ground_0517 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 3 0 Sign.leaf) = false := by
  decide

theorem ground_0518 :
    hostValue 3 (Block.variable 3 3 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0519 :
    repairedValue 3 (Block.variable 3 3 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0520 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0521 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0522 :
    hostValue 3 (Block.variable 1 0 Sign.minus) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0523 :
    repairedValue 3 (Block.variable 1 0 Sign.minus) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0524 :
    hostValue 3 (Block.variable 3 2 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0525 :
    repairedValue 3 (Block.variable 3 2 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0526 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 3 5 Sign.leaf) = false := by
  decide

theorem ground_0527 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) (Block.variable 3 5 Sign.leaf) = false := by
  decide

theorem ground_0528 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0529 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0530 :
    hostValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0531 :
    repairedValue 3 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0532 :
    hostValue 3 (Block.variable 3 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0533 :
    repairedValue 3 (Block.variable 3 0 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0534 :
    hostValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0535 :
    repairedValue 3 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0536 :
    hostValue 3 (Block.variable 2 2 Sign.minus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0537 :
    repairedValue 3 (Block.variable 2 2 Sign.minus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0538 :
    hostValue 3 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0539 :
    repairedValue 3 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0540 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0541 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0542 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 4 0 Sign.leaf) = false := by
  decide

theorem ground_0543 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.variable 4 0 Sign.leaf) = false := by
  decide

theorem ground_0544 :
    hostValue 4 (Block.variable 4 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0545 :
    repairedValue 4 (Block.variable 4 0 Sign.leaf) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0546 :
    hostValue 4 Block.dummy (Block.variable 4 0 Sign.leaf) = true := by
  decide

theorem ground_0547 :
    repairedValue 4 Block.dummy (Block.variable 4 0 Sign.leaf) = false := by
  decide

theorem ground_0548 :
    hostValue 4 Block.dummy Block.dummy = true := by
  decide

theorem ground_0549 :
    repairedValue 4 Block.dummy Block.dummy = true := by
  decide

theorem ground_0550 :
    hostValue 4 (Block.variable 4 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0551 :
    repairedValue 4 (Block.variable 4 0 Sign.leaf) Block.dummy = true := by
  decide

theorem ground_0552 :
    hostValue 4 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0553 :
    repairedValue 4 Block.dummy (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0554 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0555 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) Block.dummy = true := by
  decide

theorem ground_0556 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 2 0 Sign.minus) = false := by
  decide

theorem ground_0557 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 2 0 Sign.minus) = false := by
  decide

theorem ground_0558 :
    hostValue 4 (Block.variable 3 5 Sign.minus) (Block.variable 2 2 Sign.minus) = false := by
  decide

theorem ground_0559 :
    repairedValue 4 (Block.variable 3 5 Sign.minus) (Block.variable 2 2 Sign.minus) = false := by
  decide

theorem ground_0560 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0561 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0562 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0563 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0564 :
    hostValue 4 (Block.variable 2 0 Sign.minus) (Block.anchor { family := Family.w, depth := 4, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0565 :
    repairedValue 4 (Block.variable 2 0 Sign.minus) (Block.anchor { family := Family.w, depth := 4, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0566 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0567 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0568 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0569 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0570 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0571 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0572 :
    hostValue 4 (Block.variable 3 6 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0573 :
    repairedValue 4 (Block.variable 3 6 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0574 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0575 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0576 :
    hostValue 4 (Block.variable 4 9 Sign.leaf) (Block.variable 4 3 Sign.leaf) = false := by
  decide

theorem ground_0577 :
    repairedValue 4 (Block.variable 4 9 Sign.leaf) (Block.variable 4 3 Sign.leaf) = false := by
  decide

theorem ground_0578 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 4, parity := 0, sign := Sign.minus } 1) (Block.variable 4 0 Sign.leaf) = true := by
  decide

theorem ground_0579 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 4, parity := 0, sign := Sign.minus } 1) (Block.variable 4 0 Sign.leaf) = true := by
  decide

theorem ground_0580 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 4 14 Sign.leaf) = false := by
  decide

theorem ground_0581 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 4 14 Sign.leaf) = false := by
  decide

theorem ground_0582 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0583 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0584 :
    hostValue 4 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0585 :
    repairedValue 4 (Block.variable 1 1 Sign.plus) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0586 :
    hostValue 4 (Block.variable 4 3 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0587 :
    repairedValue 4 (Block.variable 4 3 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0588 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 4, parity := 1, sign := Sign.minus } 1) (Block.variable 2 0 Sign.minus) = false := by
  decide

theorem ground_0589 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 4, parity := 1, sign := Sign.minus } 1) (Block.variable 2 0 Sign.minus) = false := by
  decide

theorem ground_0590 :
    hostValue 4 (Block.variable 3 7 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0591 :
    repairedValue 4 (Block.variable 3 7 Sign.plus) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0592 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0593 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0594 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0595 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = true := by
  decide

theorem ground_0596 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 2 2 Sign.minus) = false := by
  decide

theorem ground_0597 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 2 2 Sign.minus) = false := by
  decide

theorem ground_0598 :
    hostValue 4 (Block.variable 4 0 Sign.leaf) (Block.variable 4 13 Sign.leaf) = true := by
  decide

theorem ground_0599 :
    repairedValue 4 (Block.variable 4 0 Sign.leaf) (Block.variable 4 13 Sign.leaf) = true := by
  decide

theorem ground_0600 :
    hostValue 4 (Block.variable 4 5 Sign.leaf) (Block.variable 3 7 Sign.plus) = true := by
  decide

theorem ground_0601 :
    repairedValue 4 (Block.variable 4 5 Sign.leaf) (Block.variable 3 7 Sign.plus) = true := by
  decide

theorem ground_0602 :
    hostValue 4 (Block.variable 4 2 Sign.leaf) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0603 :
    repairedValue 4 (Block.variable 4 2 Sign.leaf) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0604 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 3 0 Sign.minus) = false := by
  decide

theorem ground_0605 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 3 0 Sign.minus) = false := by
  decide

theorem ground_0606 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 3 2 Sign.minus) = false := by
  decide

theorem ground_0607 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 3 2 Sign.minus) = false := by
  decide

theorem ground_0608 :
    hostValue 4 (Block.variable 3 2 Sign.plus) (Block.variable 4 9 Sign.leaf) = false := by
  decide

theorem ground_0609 :
    repairedValue 4 (Block.variable 3 2 Sign.plus) (Block.variable 4 9 Sign.leaf) = false := by
  decide

theorem ground_0610 :
    hostValue 4 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0611 :
    repairedValue 4 (Block.variable 0 0 Sign.minus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0612 :
    hostValue 4 (Block.variable 4 2 Sign.leaf) (Block.variable 4 0 Sign.leaf) = false := by
  decide

theorem ground_0613 :
    repairedValue 4 (Block.variable 4 2 Sign.leaf) (Block.variable 4 0 Sign.leaf) = false := by
  decide

theorem ground_0614 :
    hostValue 4 (Block.variable 4 1 Sign.leaf) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0615 :
    repairedValue 4 (Block.variable 4 1 Sign.leaf) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0616 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0617 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 1) (Block.variable 1 0 Sign.plus) = false := by
  decide

theorem ground_0618 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0619 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0620 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0621 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0622 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 4, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0623 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 4, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0624 :
    hostValue 4 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0625 :
    repairedValue 4 (Block.variable 1 1 Sign.minus) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0626 :
    hostValue 4 (Block.variable 4 10 Sign.leaf) (Block.variable 4 6 Sign.leaf) = false := by
  decide

theorem ground_0627 :
    repairedValue 4 (Block.variable 4 10 Sign.leaf) (Block.variable 4 6 Sign.leaf) = false := by
  decide

theorem ground_0628 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 1) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0629 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 1) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0630 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 4 6 Sign.leaf) = false := by
  decide

theorem ground_0631 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 4 6 Sign.leaf) = false := by
  decide

theorem ground_0632 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0633 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0634 :
    hostValue 4 (Block.variable 3 0 Sign.minus) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0635 :
    repairedValue 4 (Block.variable 3 0 Sign.minus) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0636 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0637 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.minus } 1) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0638 :
    hostValue 4 (Block.variable 3 6 Sign.minus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0639 :
    repairedValue 4 (Block.variable 3 6 Sign.minus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0640 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0641 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 0, sign := Sign.plus } 2) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0642 :
    hostValue 4 (Block.variable 4 13 Sign.leaf) (Block.variable 4 3 Sign.leaf) = false := by
  decide

theorem ground_0643 :
    repairedValue 4 (Block.variable 4 13 Sign.leaf) (Block.variable 4 3 Sign.leaf) = false := by
  decide

theorem ground_0644 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 4, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0645 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 2) (Block.anchor { family := Family.w, depth := 4, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0646 :
    hostValue 4 (Block.variable 4 14 Sign.leaf) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0647 :
    repairedValue 4 (Block.variable 4 14 Sign.leaf) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0648 :
    hostValue 4 (Block.variable 4 5 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0649 :
    repairedValue 4 (Block.variable 4 5 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0650 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0651 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0652 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0653 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.plus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0654 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0655 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0656 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 4 8 Sign.leaf) = false := by
  decide

theorem ground_0657 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 4 8 Sign.leaf) = false := by
  decide

theorem ground_0658 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 1) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0659 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 1) (Block.variable 2 2 Sign.plus) = false := by
  decide

theorem ground_0660 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 2 2 Sign.minus) = false := by
  decide

theorem ground_0661 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) (Block.variable 2 2 Sign.minus) = false := by
  decide

theorem ground_0662 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0663 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0664 :
    hostValue 4 (Block.variable 2 2 Sign.minus) (Block.variable 4 3 Sign.leaf) = false := by
  decide

theorem ground_0665 :
    repairedValue 4 (Block.variable 2 2 Sign.minus) (Block.variable 4 3 Sign.leaf) = false := by
  decide

theorem ground_0666 :
    hostValue 4 (Block.variable 3 2 Sign.minus) (Block.variable 4 10 Sign.leaf) = false := by
  decide

theorem ground_0667 :
    repairedValue 4 (Block.variable 3 2 Sign.minus) (Block.variable 4 10 Sign.leaf) = false := by
  decide

theorem ground_0668 :
    hostValue 4 (Block.variable 4 5 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0669 :
    repairedValue 4 (Block.variable 4 5 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0670 :
    hostValue 4 (Block.variable 2 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0671 :
    repairedValue 4 (Block.variable 2 0 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0672 :
    hostValue 4 (Block.variable 3 4 Sign.plus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0673 :
    repairedValue 4 (Block.variable 3 4 Sign.plus) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.plus } 1) = true := by
  decide

theorem ground_0674 :
    hostValue 4 (Block.variable 2 2 Sign.minus) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0675 :
    repairedValue 4 (Block.variable 2 2 Sign.minus) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0676 :
    hostValue 4 (Block.variable 4 11 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0677 :
    repairedValue 4 (Block.variable 4 11 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0678 :
    hostValue 4 (Block.variable 4 5 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0679 :
    repairedValue 4 (Block.variable 4 5 Sign.leaf) (Block.anchor { family := Family.v, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0680 :
    hostValue 4 (Block.variable 4 15 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0681 :
    repairedValue 4 (Block.variable 4 15 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0682 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0683 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0684 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0685 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.minus } 1) (Block.anchor { family := Family.w, depth := 3, parity := 1, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0686 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 3 4 Sign.plus) = false := by
  decide

theorem ground_0687 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) (Block.variable 3 4 Sign.plus) = false := by
  decide

theorem ground_0688 :
    hostValue 4 (Block.variable 2 3 Sign.minus) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0689 :
    repairedValue 4 (Block.variable 2 3 Sign.minus) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0690 :
    hostValue 4 (Block.variable 4 6 Sign.leaf) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0691 :
    repairedValue 4 (Block.variable 4 6 Sign.leaf) (Block.anchor { family := Family.v, depth := 3, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0692 :
    hostValue 4 (Block.variable 4 9 Sign.leaf) (Block.variable 4 13 Sign.leaf) = true := by
  decide

theorem ground_0693 :
    repairedValue 4 (Block.variable 4 9 Sign.leaf) (Block.variable 4 13 Sign.leaf) = true := by
  decide

theorem ground_0694 :
    hostValue 4 (Block.variable 4 8 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0695 :
    repairedValue 4 (Block.variable 4 8 Sign.leaf) (Block.anchor { family := Family.w, depth := 2, parity := 0, sign := Sign.plus } 2) = false := by
  decide

theorem ground_0696 :
    hostValue 4 (Block.variable 4 8 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0697 :
    repairedValue 4 (Block.variable 4 8 Sign.leaf) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 2) = false := by
  decide

theorem ground_0698 :
    hostValue 4 (Block.variable 3 6 Sign.plus) (Block.variable 4 15 Sign.leaf) = false := by
  decide

theorem ground_0699 :
    repairedValue 4 (Block.variable 3 6 Sign.plus) (Block.variable 4 15 Sign.leaf) = false := by
  decide

theorem ground_0700 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 2) (Block.variable 4 12 Sign.leaf) = false := by
  decide

theorem ground_0701 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.minus } 2) (Block.variable 4 12 Sign.leaf) = false := by
  decide

theorem ground_0702 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0703 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 1 1 Sign.minus) = false := by
  decide

theorem ground_0704 :
    hostValue 4 (Block.variable 4 3 Sign.leaf) (Block.anchor { family := Family.w, depth := 4, parity := 1, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0705 :
    repairedValue 4 (Block.variable 4 3 Sign.leaf) (Block.anchor { family := Family.w, depth := 4, parity := 1, sign := Sign.minus } 1) = true := by
  decide

theorem ground_0706 :
    hostValue 4 (Block.variable 3 5 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0707 :
    repairedValue 4 (Block.variable 3 5 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0708 :
    hostValue 4 (Block.variable 3 5 Sign.plus) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0709 :
    repairedValue 4 (Block.variable 3 5 Sign.plus) (Block.variable 1 0 Sign.minus) = false := by
  decide

theorem ground_0710 :
    hostValue 4 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0711 :
    repairedValue 4 (Block.variable 0 0 Sign.plus) (Block.anchor { family := Family.w, depth := 1, parity := 1, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0712 :
    hostValue 4 (Block.variable 2 3 Sign.plus) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0713 :
    repairedValue 4 (Block.variable 2 3 Sign.plus) (Block.anchor { family := Family.v, depth := 4, parity := 0, sign := Sign.plus } 1) = false := by
  decide

theorem ground_0714 :
    hostValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0715 :
    repairedValue 4 (Block.anchor { family := Family.w, depth := 2, parity := 1, sign := Sign.minus } 1) (Block.variable 0 0 Sign.plus) = false := by
  decide

theorem ground_0716 :
    hostValue 4 (Block.variable 2 1 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0717 :
    repairedValue 4 (Block.variable 2 1 Sign.minus) (Block.anchor { family := Family.w, depth := 1, parity := 0, sign := Sign.minus } 1) = false := by
  decide

theorem ground_0718 :
    hostValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 3 4 Sign.plus) = false := by
  decide

theorem ground_0719 :
    repairedValue 4 (Block.anchor { family := Family.v, depth := 1, parity := 0, sign := Sign.minus } 1) (Block.variable 3 4 Sign.plus) = false := by
  decide

end H4Formal
