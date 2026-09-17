# KIPBase Blueprint

leanblueprint sources for the KIPBase formalization project.

The single chapter `src/chapters/prerequisites.tex` was migrated from
`KIP/blueprint/src/chapters/prerequisites.tex`. All `\lean{KIP.*}`
references have been rewritten to `\lean{KIPBase.*}` to match this
project's Lean module namespace.

## Layout

```
blueprint/
├── build.sh                  # lake build + leanblueprint pdf/web/checkdecls
└── src/
    ├── algtop.sty            # math macros shared with KIP
    ├── blueprint.sty         # noop \graphcolor stub
    ├── content.tex           # title + TOC + chapter include + bibliography
    ├── extra_styles.css
    ├── latexmkrc             # xelatex on print.tex
    ├── leanpkg.tex           # \dochome — point at your doc-gen4 URL
    ├── main.bib              # only HPS97 + Boardman are cited
    ├── plastex.cfg
    ├── print.tex             # PDF entry point
    ├── web.tex               # web entry point
    ├── chapters/
    │   └── prerequisites.tex # the migrated chapter
    └── macros/
        ├── common.tex        # shared (title set to "KIPBase Prerequisites")
        ├── print.tex         # PDF-only stubs for \lean / \uses / \proves
        └── web.tex           # web-only stubs (scalebox, multirow, tikz)
```

## Build

```sh
# from project root, after `pip install leanblueprint`
./blueprint/build.sh
# or, individually:
cd blueprint/src && latexmk -pdf print.tex      # PDF only
cd blueprint && leanblueprint web               # HTML only
cd blueprint && leanblueprint checkdecls        # verify \lean{} decls exist
```

## Customization checklist

- `src/leanpkg.tex` — set `\dochome{...}` to the doc-gen4 GitHub Pages URL
  for KIPBase once it is set up.
- `src/macros/common.tex` — adjust title/author block as the project grows.
- `src/main.bib` — add references as new chapters cite them.
