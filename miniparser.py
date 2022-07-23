import re

class ParseError(Exception): ...

def pregex(word):
    def _pregex(inp):
        if not inp:
            raise ParseError("End of file")
        match = re.match(rf"\s*({word})", inp)
        if match is not None:
            return match.group(1), inp[match.end(1) :]
        raise ParseError(f"Epxect {word} found {inp}")

    return _pregex

def pand(*parsers):
    def _pall(inp):
        results = []
        for p in parsers:
            res, inp = p(inp)
            results.append(res)
        return results, inp

    return _pall

def por(*parsers):
    def _por(inp):
        for p in parsers:
            try:
                return p(inp)
            except ParseError:
                continue
        raise ParseError(f"Expect any of {parsers}, but no match")
    return _por
