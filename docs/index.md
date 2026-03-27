# A TypeTopology Website

This website was generated from the Agda source files in a ***[FORK]*** of the
[TypeTopology repository] using a *[Makefile]* (copied from the
[Agda-Material template], with minor adjustments).

!!! warning

    The current **definitive [TypeTopology website]** is generated directly
    from the Agda files in the [TypeTopology repository]. Some of the Agda
    files in the fork from which the present website was generated may be
    outdated.

The theme *[Material for MkDocs]* with the *[Awesome-Nav]* plugin generates the
hierarchical navigation menus from the directory structure of the repository
and the `nav` specification in the file *[docs/.nav.yml]*. 

The *[Modules]* section lists an `index` module that imports the `index` for
for each part of the TypeTopology library. The section also includes
[AllModulesIndex], which is the main index, in the sense of being the only one
which imports everything else recursively, while [index] is the index of
`--safe` things which strictly use the philosophy of TypeTopology.

!!! info

    This website was deployed from the `gen-website` branch of the repository.

This website was generated from a [fork] of the TypeTopology repository
after copying the following files from the [Agda-Material template]:

- `Makefile`
- `mkdocs.yml`
- `docs/*`

`Makefile`, `mkdocs.yml`, and `docs/.nav.yml` required minor editing.
The `docs/*.md` files were replaced by the `docs/index.md` file containing the
source for the current page. The shell script `docs/updatehtml` was copied
from `admin-utilities/updatehtml`.

The shell commands used to check the Agda sources, then generate and browse
this website, were:

```sh
make check
make web
make serve
```

The following command was used to deploy the generated website to GitHub Pages:

```sh
make deploy
```

(Further commands can be used to deploy a versioned website.)

The approximate times taken by the above commands were:

- `make check`: 15 seconds
- `make web`: 100 seconds
- `make serve`: 75 seconds
- `make deploy`: 100 seconds

!!! note

    The 850+ Agda modules in the repository fork had previously been checked.

Running [linkcheck]:

```sh
linkcheck/linkcheck -e localhost:8010 --skip-file skip.txt
Perfect. Checked 3105604 links, 1867 destination URLs (1 ignored).
```

## Agda-Material

The [Agda-Material template] supports **generation of websites** with
**highlighted, hyperlinked listings** of (plain or literate) Agda source code.
See the [Agda-Material] website for how to install and use the template, and
for some test modules.

[Agda-Material]: https://pdmosses.github.io/agda-material/
[Agda-Material template]: https://github.com/pdmosses/agda-material/
[Material for MkDocs]: https://squidfunk.github.io/mkdocs-material/
[Awesome-Nav]: https://lukasgeiter.github.io/mkdocs-awesome-nav/
[mike]: https://github.com/jimporter/mike/
[linkcheck]: https://github.com/filiph/linkcheck/

[TypeTopology repository]: https://github.com/martinescardo/TypeTopology/
[TypeTopology website]: https://martinescardo.github.io/TypeTopology/

[FORK]: https://github.com/pdmosses/TypeTopology/tree/gen-website
[Makefile]: https://github.com/pdmosses/TypeTopology/blob/gen-website/Makefile
[docs/.nav.yml]: https://github.com/pdmosses/TypeTopology/blob/gen-website/docs/.nav.yml
[index]: index/index.md
[Modules]: index/index.md
[AllModulesIndex]: AllModulesIndex/index.md
[HTML]: AllModulesIndex.html