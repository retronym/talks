import java.util.*;

/** A minimal JSON reader for the probe's input: objects, arrays, strings, booleans, null. */
final class Json {
  private final String s;
  private int i;

  private Json(String s) { this.s = s; }

  static Object parse(String s) {
    Json j = new Json(s);
    Object v = j.value();
    j.ws();
    if (j.i != s.length()) throw new IllegalArgumentException("trailing input at " + j.i);
    return v;
  }

  private void ws() { while (i < s.length() && Character.isWhitespace(s.charAt(i))) i++; }

  private Object value() {
    ws();
    char c = s.charAt(i);
    switch (c) {
      case '{': {
        i++;
        Map<String, Object> m = new LinkedHashMap<>();
        ws();
        if (s.charAt(i) == '}') { i++; return m; }
        while (true) {
          ws();
          String k = string();
          ws(); expect(':');
          m.put(k, value());
          ws();
          if (s.charAt(i) == ',') { i++; continue; }
          expect('}');
          return m;
        }
      }
      case '[': {
        i++;
        List<Object> l = new ArrayList<>();
        ws();
        if (s.charAt(i) == ']') { i++; return l; }
        while (true) {
          l.add(value());
          ws();
          if (s.charAt(i) == ',') { i++; continue; }
          expect(']');
          return l;
        }
      }
      case '"': return string();
      default:
        if (s.startsWith("true", i)) { i += 4; return Boolean.TRUE; }
        if (s.startsWith("false", i)) { i += 5; return Boolean.FALSE; }
        if (s.startsWith("null", i)) { i += 4; return null; }
        throw new IllegalArgumentException("unexpected '" + c + "' at " + i);
    }
  }

  private void expect(char c) {
    if (s.charAt(i) != c) throw new IllegalArgumentException("expected '" + c + "' at " + i);
    i++;
  }

  private String string() {
    expect('"');
    StringBuilder b = new StringBuilder();
    while (s.charAt(i) != '"') {
      char c = s.charAt(i++);
      if (c == '\\') {
        char e = s.charAt(i++);
        b.append(e == 'n' ? '\n' : e);
      } else b.append(c);
    }
    i++;
    return b.toString();
  }

  @SuppressWarnings("unchecked")
  static Map<String, Object> obj(Object o) { return (Map<String, Object>) o; }

  @SuppressWarnings("unchecked")
  static List<Object> arr(Object o) { return (List<Object>) o; }

  static List<Map<String, Object>> objs(Object o) {
    List<Map<String, Object>> r = new ArrayList<>();
    for (Object x : arr(o)) r.add(obj(x));
    return r;
  }
}
