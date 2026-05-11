# What Proof Mode does

NiceGeo can write proofs as **tactic scripts** between **`Proof.`** and **`Qed.`**. With **Proof Mode** on, the extension asks the server: “what is the proof state **up to this position** in the script?”

So the **Proof State** view is **cursor-driven**:

- Unfinished tactic line → that tactic is not applied yet in the snapshot.
- End of line / after it → it is applied.
- After **`Qed.`** → the whole script is treated as finished for that theorem.

You will open a **bundled tutorial file** that starts with several `Proof.` … `Qed.` blocks, then optional hover practice. Keep this walkthrough open in one column and the `.ncg` file beside it.
