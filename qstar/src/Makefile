SRC_FILES=$(wildcard *.fst *.fsti)
OUT_DIR=output
FSTAR=fstar.exe --cache_checked_modules --cache_dir $(OUT_DIR) --odir $(OUT_DIR) $(OTHERFLAGS) --already_cached Prims,FStar

all: verify_all

.depend:
	$(FSTAR) --dep full $(SRC_FILES) > ._depend
	mv ._depend .depend

depend: .depend

include .depend

%.fst.checked:
	$(FSTAR) $<

%.fsti.checked:
	$(FSTAR) $<

$(OUT_DIR):
	mkdir -p $(OUT_DIR)

verify_all: $(OUT_DIR) $(ALL_CHECKED_FILES)

clean:
	rm -rf $(OUT_DIR) .depend ._depend
