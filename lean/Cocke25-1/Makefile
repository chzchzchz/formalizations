MATHLIB_CACHE_STAMP := .lake/mathlib-cache.stamp
CACHE_SENTINEL := .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Logic/Basic.olean

.PHONY: all cache clean
all:
	@if [ ! -f $(MATHLIB_CACHE_STAMP) ] \
	    || [ ! -f $(CACHE_SENTINEL) ]; then \
	  lake exe cache get! && touch $(MATHLIB_CACHE_STAMP); \
	else \
	  echo "mathlib cache up to date, skipping fetch"; \
	fi
	lake build

cache:
	rm -f $(MATHLIB_CACHE_STAMP)
	lake exe cache get!
	touch $(MATHLIB_CACHE_STAMP)

clean:
	rm -rf .lake/build
