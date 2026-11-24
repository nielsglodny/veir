// RUN: lake env veir-interpret --ctree %s | filecheck %s

// `x` is satisfiable, so `smt.check` runs its first region.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %result = "smt.solver"() ({
      %x = "smt.declare_fun"() : () -> !smt.bool
      "smt.assert"(%x) : (!smt.bool) -> ()
      %r = "smt.check"() ({
        %c1 = "arith.constant"() <{value = 1 : i32}> : () -> i32
        "smt.yield"(%c1) : (i32) -> ()
      }, {
        %c0 = "arith.constant"() <{value = 0 : i32}> : () -> i32
        "smt.yield"(%c0) : (i32) -> ()
      }, {
        %cm1 = "arith.constant"() <{value = -1 : i32}> : () -> i32
        "smt.yield"(%cm1) : (i32) -> ()
      }) : () -> i32
      "smt.yield"(%r) : (i32) -> ()
    }) : () -> i32
    "func.return"(%result) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
