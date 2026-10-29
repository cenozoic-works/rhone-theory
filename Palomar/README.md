# Palomar registry entries

Results are attributed to models from OpenAI, Anthropic, Meta, internal models, and human experts.

Each `Challenge.lean` imports its body from `Rhone/Unproved/Palomar/<Entry>/`. An alignment
source "This project" means the proof was written here; its novelty is unknown and no priority
is claimed.

Other formalizations of overlapping results are listed in `sources` (type `other`,
with the repository at a fixed commit, the files and declarations, and the level of overlap) and
in `related_formalizations` (relationship `independent`). They were developed independently of
this repository. No order of priority is stated in either direction.

The Challenges use `attribute [-instance]`, `clear_aux_proof_cache`, and `set_main_module` so
that generated auxiliary declarations match the library. They change no statement. In 12
Challenges `clear_aux_proof_cache` calls `evalConst`, which is `unsafe`.

Each Challenge sets `maxSynthPendingDepth` to 3, the value in `lakefile.lean`, because Palomar
compiles the Challenge without the Lake configuration. Without it, instance search can elaborate
a statement differently from the library.

    lake comparator --config Palomar/<Entry>/comparator.json
    lake env lean --run tools/palomar/Check.lean Palomar/<Entry>/comparator.json
