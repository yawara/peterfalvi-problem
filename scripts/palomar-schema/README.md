# Pinned metadata inputs

These files support the offline check `python3 scripts/check_palomar_metadata.py`. It checks
the shape and consistency of `formalization.yaml` and `comparator.json`. It does not run
Comparator, check the mathematics, or stand for a Palomar review.

## Upstream schema

`v0.4.schema.json` is copied unchanged from
[mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml/blob/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json),
commit `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`. It is distributed under Apache-2.0; the
upstream license text is `LICENSE`. The check reads this local file and does not fetch the
schema.

The root `LICENSE` of this repository must equal this standard Apache-2.0 text, and the metadata
must declare `Apache-2.0`.

## Classification snapshots

`arxiv-codes.json` and `msc2020-codes.json` are the sorted keys of the
[PalomarSubmission taxonomy files](https://github.com/PalomarRegistry/PalomarSubmission/tree/ef2fa1eadcb246c2346ddba39b52eaa53d4bb763/taxonomies)
`arxiv-categories.json` and `msc2020-codes.json` at commit
`ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`, written as `json.dumps(sorted(data), indent=2) + "\n"`.
The upstream MIT license and copyright notice are in `PALOMAR-LICENSE`.

| File | SHA256 |
| --- | --- |
| `v0.4.schema.json` | `25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce` |
| `LICENSE` | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `arxiv-codes.json` | `aca149ce8d56144aebd1d12ff0bfbe67bd412f36b8401a88704635ff20c24911` |
| `msc2020-codes.json` | `711221fc1a61ac16efd153086836dc3e6debd256de0aef5b41616e75ea4b0333` |
| `PALOMAR-LICENSE` | `10321b0cca2b8025d4b5065dd20e22c1f74da2e872c12363e3601974e093bc21` |
