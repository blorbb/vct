EXTRA_DIR:= doc-config
COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
	-d docs \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS
PUBLIC_URL := "https://blorbb.github.io/vct"
SUBDIR_ROOTS := theories
DIRS := . $(shell find $(SUBDIR_ROOTS) -type d)
BUILD_PATTERNS := *.vok *.vos *.glob *.vo .*.aux
BUILD_FILES := $(foreach DIR,$(DIRS),$(addprefix $(DIR)/,$(BUILD_PATTERNS)))

_: makefile.rocq

# Create Rocq makefile and compile.
makefile.rocq:
	rocq makefile -f _CoqProject -docroot docs -o $@

# Generate Rocq documentation.
doc: makefile.rocq
	rm -rf html docs/*
	COQDOCEXTRAFLAGS='--external $(PUBLIC_URL)'
	@$(MAKE) -f makefile.rocq html
	cp html/* docs
	cp $(EXTRA_DIR)/resources/* docs

-include makefile.rocq

# Remove Rocq generated files and OCaml extracted files.
clean::
	rm makefile.rocq makefile.rocq.conf
	rm -f $(BUILD_FILES)
	find src/lib -maxdepth 1 -type f \
		! -name 'dune' ! -name 'bindings.ml' ! -name 'bindings.mli' \
		! -name 'lexer.mll' ! -name 'parser.mly' -delete

.PHONY: _
