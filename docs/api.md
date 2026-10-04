# The HTTP search API

One endpoint, no key, no sign-up:

```
GET https://competemath.com/api/tengoku/search?q=<query>
```

`q` is the only parameter — a declaration name (`Nat.add_comm`), a fragment of
one (`sum_sq`), or plain English (`sum of two squares`) — URL-encoded. An empty
`q` returns no results.

Vercel's standard security measures are enabled on this endpoint: traffic that
looks like an attack (floods, bursts from many addresses, known bad clients) is
challenged or blocked by the platform before it reaches the API, with a `403` or
`429`. Honest use at a few requests a second is not what those measures target.

## Response

`200 application/json`, up to 30 results, best match first:

```json
{
  "results": [
    {
      "id": 3979306448,
      "name": "Nat.add_comm",
      "statement": "∀ (n m : ℕ), n + m = m + n",
      "status": "trusted",
      "library": "mathlib",
      "sourceUrl": "https://github.com/competemath/tengoku/blob/8cfa337c09cfc7ade3b3f024cfa82a436f700349/Init/Data/Nat/Basic.lean#L158",
      "proof": "",
      "toolchain": "",
      "compatibleToolchains": []
    }
  ]
}
```

| field | meaning |
|---|---|
| `name` | the declaration's full name, as in Lean |
| `statement` | its type, fully elaborated |
| `status` | `trusted` — compiled by the tree's own toolchain; `staging` — a verified translation not yet built into the tree; `tentative` — a real proof from its source, not yet re-verified here |
| `library` | the source it came from (`mathlib`, `carleson`, …) |
| `sourceUrl` | where the declaration lives, proof included: for `trusted` entries the line in the tree's Lean source (`Tengoku/…`, `Init/…`), for the rest the line in the library it was harvested from |
| `id` | stable within one index build only; don't persist it |

`proof`, `toolchain` and `compatibleToolchains` are empty in search results
today; the proof is at `sourceUrl`.

## Using it well

- **Know the name?** Put it in `q`; it comes back first.
- **Don't?** Describe it. The index matches meaning as well as text:
  `q=continuous image of compact is compact`.
- **Prefer `trusted`.** It is what the tree actually compiles. `tentative` is
  real mathematics from a real source that nobody has re-verified on this
  toolchain yet.
- **As prover context:** `statement` is the type to state or `exact`, and
  `name` resolves in any project that imports the tree. Give a prover the top
  few results, not all thirty.
- **Be reasonable.** There is no key and no published rate limit; a few
  requests a second is fine, an agent loop hammering it is not. Cache what you
  have already asked.
- **Call it from a backend or an agent**, not from a browser page on another
  origin — no CORS headers are set.
- The same index, from an editor or agent: the MCP server at
  `https://barkingtree-leak-i.hf.space/sse` (`loogle_search` for type
  patterns such as `_ * _ = _ * _`, `moogle_search` for meaning).

## Examples

```bash
curl 'https://competemath.com/api/tengoku/search?q=Nat.add_comm'
```

```python
import requests
hits = requests.get("https://competemath.com/api/tengoku/search",
                    params={"q": "sum of two squares"}, timeout=30).json()["results"]
for h in hits[:5]:
    print(h["status"], h["name"], "—", h["statement"])
```

```js
const q = encodeURIComponent("continuous image of compact is compact");
const { results } = await fetch(`https://competemath.com/api/tengoku/search?q=${q}`).then(r => r.json());
```
