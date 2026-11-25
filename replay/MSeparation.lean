import Lean
import OpenCausalScience.Papers.AliRichardsonSpirtes2009.Figures4And6
import OpenCausalScience.Papers.RichardsonSpirtes2002.Figure9

open OpenCausalScience

def caseGraphs : List (String × MarkedGraph 4) :=
  let f9 := ("9a", RichardsonSpirtes2002.Figure9.graph)
  let f9b := ("9b", RichardsonSpirtes2002.Figure9.extension)
  let f4 := [("4.G1", AliRichardsonSpirtes2009.Figure4.first),
    ("4.G2", AliRichardsonSpirtes2009.Figure4.second),
    ("4.G3", AliRichardsonSpirtes2009.Figure4.third)]
  let f6 := [("6.i.G1", AliRichardsonSpirtes2009.Figure6.firstI),
    ("6.i.G2", AliRichardsonSpirtes2009.Figure6.secondI),
    ("6.ii.G1", AliRichardsonSpirtes2009.Figure6.firstII),
    ("6.ii.G2", AliRichardsonSpirtes2009.Figure6.secondII)]
  [f9, f9b] ++ f4 ++ f6

def signature (graph : MarkedGraph 4) : List Bool :=
  (List.finRange 4).flatMap fun left =>
    (List.finRange 4).flatMap fun right =>
      (List.finRange 16).filterMap fun raw =>
        let set : BitVec 4 := BitVec.ofFin raw
        if left != right && !MarkedGraph.conditioned set left &&
            !MarkedGraph.conditioned set right then
          some (graph.mConnected left right set)
        else none

#eval IO.println ((Lean.toJson (caseGraphs.map fun (name, graph) =>
  (name, signature graph))).compress)
