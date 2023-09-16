# index-core takes 3.58 minutes.
# index takes 8.97 minutes without parallelisation.
# index Takes 7.8 minutes with -j 8.

all: _build/2.6.3/agda/source/index.agdai

build_dir    := _build/2.6.3/agda/source

core_deps    := $(build_dir)/W/index.agdai               \
                $(build_dir)/ContinuityAxiom/index.agdai \
                $(build_dir)/Categories/index.agdai      \
                $(build_dir)/Naturals/index.agdai

index_core   := $(build_dir)/index-core.agdai

index        := $(build_dir)/index-core.agdai

developments := $(build_dir)/Integers/index.agdai         \
                $(build_dir)/Various/index.agdai          \
                $(build_dir)/DyadicsInductive/index.agdai \
                $(build_dir)/TWA/index.agdai              \
                $(build_dir)/Relations/index.agdai        \
                $(build_dir)/Lifting/index.agdai          \
                $(build_dir)/DomainTheory/index.agdai     \
                $(build_dir)/Locales/index.agdai          \
                $(build_dir)/EffectfulForcing/index.agdai \
                $(build_dir)/Groups/index.agdai           \
                $(build_dir)/Duploids/index.agdai         \
                $(build_dir)/BinarySystems/index.agdai    \
                $(build_dir)/Modal/index.agdai            \
                $(build_dir)/TypeTopology/index.agdai     \
                $(build_dir)/Field/index.agdai

_build/2.6.3/agda/source/index-kernel.agdai:
	agda --safe source/index-kernel.lagda > /dev/null
	touch $@

## Files that depend only on index-kernel

_build/2.6.3/agda/source/ContinuityAxiom/index.agdai: _build/2.6.3/agda/source/index-kernel.agdai
	agda --safe source/ContinuityAxiom/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Categories/index.agdai: _build/2.6.3/agda/source/index-kernel.agdai
	agda --safe source/Categories/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/W/index.agdai: _build/2.6.3/agda/source/index-kernel.agdai
	agda --safe source/W/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Naturals/index.agdai: _build/2.6.3/agda/source/index-kernel.agdai
	agda --safe source/Naturals/index.lagda > /dev/null
	touch $@

## index-core which depends on the core files

_build/2.6.3/agda/source/index-core.agdai: $(core_deps)
	agda --safe source/index-core.lagda > /dev/null
	touch $@

## Developments

_build/2.6.3/agda/source/Integers/index.agdai: $(index_core)
	agda --safe source/Integers/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/DyadicsInductive/index.agdai: $(index_core)
	agda --safe source/DyadicsInductive/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/DomainTheory/index.agdai: $(index_core) _build/2.6.3/agda/source/DyadicsInductive/index.agdai
	agda --safe source/DomainTheory/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Locales/index.agdai: $(index_core) _build/2.6.3/agda/source/DomainTheory/index.agdai
	agda --safe source/Locales/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/TWA/index.agdai: $(index_core)
	agda --safe source/TWA/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Relations/index.agdai: $(index_core)
	agda --safe source/Relations/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Lifting/index.agdai: $(index_core)
	agda --safe source/Lifting/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Various/index.agdai: $(index_core)
	agda --safe source/Various/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/EffectfulForcing/index.agdai: $(index_core)
	agda --safe source/EffectfulForcing/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Groups/index.agdai: $(index_core)
	agda --safe source/Groups/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Duploids/index.agdai: $(index_core)
	agda --safe source/Duploids/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/BinarySystems/index.agdai: $(index_core)
	agda --safe source/BinarySystems/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Modal/index.agdai: $(index_core)
	agda --safe source/Modal/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Dyadics/index.agdai: $(index_core)
	agda --safe source/Dyadics/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/TypeTopology/index.agdai: $(index_core)
	agda --safe source/TypeTopology/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/Field/index.agdai: $(index_core) _build/2.6.3/agda/source/TypeTopology/index.agdai
	agda --safe source/Field/index.lagda > /dev/null
	touch $@

_build/2.6.3/agda/source/index.agdai: $(developments)
	agda --safe source/index.lagda
	touch $@

.PHONY: clean
clean:
	rm -rf _build
