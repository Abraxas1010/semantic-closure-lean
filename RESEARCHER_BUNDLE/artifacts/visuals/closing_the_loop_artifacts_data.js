// Extra artifact links keyed by Lean declaration name.
// This is loaded by the 2D/3D viewers to make the “proof ↔ artifacts” mapping explicit.

window.CLOSING_THE_LOOP_ARTIFACTS = {
  byDecl: {
    // Computation hook: proof ↔ extracted code ↔ in-browser execution
    "HeytingLean.ClosingTheLoop.Semantics.LambdaIRBridge.eval_beta": {
      links: [
        { label: "Run: WASM demo (add1)", href: "./compute_add1.html" },
        { label: "LambdaIR: add1.lambdair.txt", href: "../compiler/ir/add1.lambdair.txt" },
        { label: "MiniC: add1.minic.txt", href: "../compiler/ir/add1.minic.txt" },
        { label: "C: add1.c", href: "../compiler/c/add1.c" },
        { label: "C (WASM): add1_wasm.c", href: "../compiler/c/add1_wasm.c" }
      ]
    },

    // ClosingTheLoop headline proofs
    "HeytingLean.ClosingTheLoop.MR.closeSelector.idem": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_ClosingTheLoop_MR_closeSelector_idem.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_ClosingTheLoop_MR_closeSelector_idem.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_ClosingTheLoop_MR_closeSelector_idem.json" }
      ]
    },
    "HeytingLean.ClosingTheLoop.Cat.curryNatIso": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_curryNatIso.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_curryNatIso.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_curryNatIso.json" }
      ]
    },
    "HeytingLean.ClosingTheLoop.Cat.idem_of_yoneda_map_idem": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_idem_of_yoneda_map_idem.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_idem_of_yoneda_map_idem.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_idem_of_yoneda_map_idem.json" }
      ]
    },
    "HeytingLean.ClosingTheLoop.Cat.map_close_eq": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_map_close_eq.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_map_close_eq.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Cat_map_close_eq.json" }
      ]
    },
    "HeytingLean.ClosingTheLoop.Semantics.FunctorialTime.futureKernel.idem": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Semantics_FunctorialTime_futureKernel_idem.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Semantics_FunctorialTime_futureKernel_idem.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Semantics_FunctorialTime_futureKernel_idem.json" }
      ]
    },
    "HeytingLean.ClosingTheLoop.Semantics.Realizability.realizable_invariant_of_simulation": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Semantics_Realizability_realizable_invariant_of_simulation.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Semantics_Realizability_realizable_invariant_of_simulation.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_ClosingTheLoop_Semantics_Realizability_realizable_invariant_of_simulation.json" }
      ]
    },

    // Noneism headline proofs (bridge: dynamics ↔ β)
    "HeytingLean.Noneism.Eigen.determined_by_dynamics": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_Noneism_Eigen_determined_by_dynamics.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_Noneism_Eigen_determined_by_dynamics.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_Noneism_Eigen_determined_by_dynamics.json" }
      ]
    },
    "HeytingLean.Noneism.Bridge.selectorDynamics_stable_iff": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_Noneism_Bridge_selectorDynamics_stable_iff.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_Noneism_Bridge_selectorDynamics_stable_iff.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_Noneism_Bridge_selectorDynamics_stable_iff.json" }
      ]
    },
    "HeytingLean.Noneism.Bridge.selectorDynamics_unique_stable": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_Noneism_Bridge_selectorDynamics_unique_stable.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_Noneism_Bridge_selectorDynamics_unique_stable.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_Noneism_Bridge_selectorDynamics_unique_stable.json" }
      ]
    },
    "HeytingLean.Noneism.Bridge.beta_right_inverse": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_right_inverse.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_right_inverse.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_right_inverse.json" }
      ]
    },
    "HeytingLean.Noneism.Bridge.beta_stable": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_stable.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_stable.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_stable.json" }
      ]
    },
    "HeytingLean.Noneism.Bridge.beta_eq_const": {
      links: [
        { label: "Proof DAG (SVG)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_eq_const.svg" },
        { label: "Proof DAG (DOT)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_eq_const.dot" },
        { label: "Proof DAG (JSON)", href: "./proof_dags/HeytingLean_Noneism_Bridge_beta_eq_const.json" }
      ]
    }
  }
}

