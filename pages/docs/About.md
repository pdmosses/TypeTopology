# An Alternative TypeTopology Website

This website illustrates and tests use of **[Agda-Pages]** to
**generate websites** with **module navigation** between
**highlighted, hyperlinked listings** of Agda code.

## About the website

The website was generated from the Agda source files in the [add-pages branch]
of a **[fork]** of the [TypeTopology repository].

!!! warning
    The current *definitive* [TypeTopology website] is generated directly
    from the Agda files in the [TypeTopology repository]. Some of the Agda
    files in the fork from which the present website was generated may be
    outdated, resulting in outdated webpages.

The **[Modules]** section includes the [index] webpage generated from the
top-level Agda module that imports `--safe` modules which strictly use the
philosophy of TypeTopology. The [Modules] section also includes the
[AllModulesIndex] webpage generated from the Agda module which imports
everything else recursively.

See the **[Agda-Pages About]** page for an overview of the features
of the generated website, and for links to further examples.

## Generation

The **[Agda-Pages User Guide]** explains how to generate a website listing
Agda code in any GitHub repository.

See the **[Agda-Pages README]** for how to install Agda-Pages,
and for a list of its main software dependencies.

The following files were added to the fork of the TypeTopology repository
to support website generation using Agda-Pages:


```
.
├─  ...
└─  pages/
    ├─  agda-pages/
    │   └─ ...
    ├─  docs/
    │   ├─ About.md
    │   └─ .nav.yml
    ├─  Makefile
    └─  mkdocs.yml
```

The [pages directory] includes all the required files:

-   `agda-pages` was added as a Git submodule referring to the
    [Agda-Pages repository].
-   [docs/About.md] is the source file for the present webpage.
-   [docs/.nav.yml] configures the main navigation of the website.
-   [Makefile] configures the location of the Agda source files and
    a non-generated Markdown file.
-   [mkdocs.yml] configures the name and location of the website and the
    repository.

Running the following shell commands in the [pages directory] then generated
the present website:

```shell
make check
make web
make serve
```

While serving the website at `localhost:8010`, running the [linkcheck] application
reported:

```sh
Perfect. Checked 2180364 links, 1015 destination URLs (1 ignored).
```

The generated website was deployed at <https://pdmosses.github.io/TypeTopology/> by:

```shell
make deploy
```

[Agda-Pages]:            https://pdmosses.github.io/agda-pages/
[Agda-Pages About]:      https://pdmosses.github.io/agda-pages/About/
[Agda-Pages User Guide]: https://pdmosses.github.io/agda-pages/User-Guide/
[Agda-Pages repository]: https://github.com/pdmosses/agda-pages/
[Agda-Pages README]:     https://github.com/pdmosses/agda-pages/blob/main/README.md
[linkcheck]:             https://github.com/filiph/linkcheck/

[index]:                 index.md
[Modules]:               index.md
[AllModulesIndex]:       AllModulesIndex.md

[fork]:                  https://github.com/pdmosses/TypeTopology
[add-pages branch]:      https://github.com/pdmosses/TypeTopology/tree/add-pages
[pages directory]:       https://github.com/pdmosses/TypeTopology/tree/add-pages/pages
[docs/.nav.yml]:         https://github.com/pdmosses/TypeTopology/blob/add-pages/pages/docs/.nav.yml
[docs/About.md]:         https://github.com/pdmosses/TypeTopology/blob/add-pages/pages/docs/About.md
[Makefile]:              https://github.com/pdmosses/TypeTopology/blob/add-pages/pages/Makefile
[mkdocs.yml]:            https://github.com/pdmosses/TypeTopology/blob/add-pages/pages/mkdocs.yml

[TypeTopology repository]: https://github.com/martinescardo/TypeTopology/
[TypeTopology website]:    https://martinescardo.github.io/TypeTopology/
