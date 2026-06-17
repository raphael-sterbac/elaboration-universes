GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[0;33m'
NC='\033[0m' 

CMD="cabal exec implem-fuss-free -- nf"

TOTAL=0
PASSED=0
FAILED=0

echo -e "${YELLOW}Passing tests${NC}"
for file in test/pass/*; do
    if [ -f "$file" ]; then
        TOTAL=$((TOTAL + 1))
        
        OUTPUT=$($CMD "$file" 2>&1)
        EXIT_CODE=$?

        if [ $EXIT_CODE -eq 0 ]; then
            echo -e "${GREEN}PASS${NC} $file"
            PASSED=$((PASSED + 1))
        else
            echo -e "${RED}FAIL${NC} $file (Expected to pass, but did not typecheck)"
            echo -e "${RED}Output:${NC}"
            echo "$OUTPUT" | sed 's/^/       /' 
            FAILED=$((FAILED + 1))
        fi
    fi
done

echo ""
echo -e "${YELLOW}Failing tests${NC}"
for file in test/fail/*; do
    if [ -f "$file" ]; then
        TOTAL=$((TOTAL + 1))
        
        OUTPUT=$($CMD "$file" 2>&1)
        EXIT_CODE=$?

        if [ $EXIT_CODE -eq 1 ]; then
            echo -e "${GREEN}PASS${NC} $file"
            PASSED=$((PASSED + 1))
        else
            echo -e "${RED}FAIL${NC} $file (Expected to fail, but typechecked)"
            FAILED=$((FAILED + 1))
        fi
    fi
done

echo ""
echo -e "Total:  $TOTAL"

if [ $FAILED -gt 0 ]; then
    echo -e "${GREEN}Passed: $PASSED${NC}"
    echo -e "${RED}Failed: $FAILED${NC}"
    echo -e "${RED}Some tests failed.${NC}"
    exit 1
else
    echo -e "${GREEN}Passed: $PASSED${NC}"
    echo -e "${RED}Failed: $FAILED${NC}"
    echo -e "${GREEN}All tests completed successfully${NC}"
    exit 0
fi