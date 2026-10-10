import java.lang.reflect.InvocationTargetException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.*;
import java.util.*;

/**
 * Runs each rendered case's client against `v0` and `v1` and compares the outcome with the model's.
 * Plain Java 17, so it runs on JDK 21 as well as on the JDK that rendered the classfiles.
 *
 * A client loads its classes (`Class.forName(x, false, l)`: loading, with the supertype and
 * final-override checks), then runs each site. A site's receiver is instantiated reflectively first;
 * if the receiver's class cannot be instantiated (an interface or abstract class in that world) the
 * site gets `null`, and resolution still happens before the null check.
 *
 * Usage: java -cp classes Run cases.jsonl out
 * Prints one TSV row per case and world: case, world, model, JVM, agree, JVM message.
 */
public class Run {
  /** The model's `LinkError` constructors, with the JVM class each maps to. */
  static final Map<String, String> ERRORS = Map.of(
      "noClassDef", "java.lang.NoClassDefFoundError",
      "incompatibleClassChange", "java.lang.IncompatibleClassChangeError",
      "noSuchMethod", "java.lang.NoSuchMethodError",
      "abstractMethod", "java.lang.AbstractMethodError",
      "instantiation", "java.lang.InstantiationError",
      // HotSpot's class file parser, on JDK 21, 25 and 27; not the VerifyError older JDKs threw.
      "finalSuper", "java.lang.IncompatibleClassChangeError",
      "finalOverride", "java.lang.IncompatibleClassChangeError");

  public static void main(String[] args) throws Exception {
    Path out = Path.of(args[1]);
    int disagree = 0;
    for (String line : Files.readAllLines(Path.of(args[0]))) {
      if (line.isBlank()) continue;
      Map<String, Object> k = Json.obj(Json.parse(line));
      String name = (String) k.get("name");
      for (String w : List.of("v0", "v1")) {
        String model = expected(Json.obj(k.get(w.equals("v0") ? "before" : "after")));
        String[] jvm = run(out.resolve(name), w, k);
        String verdict = model.equals(jvm[0]) ? "agree" : known(model, jvm) ? "known JDK-8356942" : "DISAGREE";
        if (verdict.equals("DISAGREE")) disagree++;
        System.out.println(name + "\t" + w + "\t" + model + "\t" + jvm[0] + "\t" + verdict + "\t" + jvm[1]);
      }
    }
    System.out.println("# " + System.getProperty("java.vm.version") + ": " + disagree + " disagreements");
    if (disagree > 0) System.exit(1);
  }

  /**
   * JDK-8356942 (fixed in 25): since JDK 10, `invokeinterface` on a receiver with conflicting
   * default methods throws AbstractMethodError, where JVMS §6.5 and `invokevirtual` say
   * IncompatibleClassChangeError.
   */
  static boolean known(String model, String[] jvm) {
    return Runtime.version().feature() < 25 && model.equals("java.lang.IncompatibleClassChangeError")
        && jvm[0].equals("java.lang.AbstractMethodError");
  }

  static String expected(Map<String, Object> o) {
    if (o.containsKey("error")) return ERRORS.get((String) o.get("error"));
    return "ok " + Json.arr(o.get("ok"));
  }

  static String[] run(Path dir, String world, Map<String, Object> k) throws Exception {
    URL[] cp = { url(dir.resolve("client")), url(dir.resolve("sites")), url(dir.resolve(world)) };
    try (URLClassLoader l = new URLClassLoader(cp, Run.class.getClassLoader())) {
      List<String> ran = new ArrayList<>();
      try {
        for (Object x : Json.arr(k.get("loads"))) Class.forName((String) x, false, l);
        List<Map<String, Object>> sites = Json.objs(k.get("sites"));
        for (int i = 0; i < sites.size(); i++) {
          Map<String, Object> s = sites.get(i);
          Object recv = s.get("recv") == null ? null : instantiate((String) s.get("recv"), l);
          ProbeLog.last = null;
          try {
            Class.forName("Site" + i, true, l).getMethod("run", Object.class).invoke(null, recv);
          } catch (InvocationTargetException e) {
            throw e.getCause();
          }
          ran.add(s.get("op").equals("new") ? (String) s.get("owner") : ProbeLog.last);
        }
        return new String[] { "ok " + ran, "" };
      } catch (Throwable t) {
        return new String[] { t.getClass().getName(), String.valueOf(t.getMessage()) };
      }
    }
  }

  static Object instantiate(String c, ClassLoader l) throws Throwable {
    Class<?> k = Class.forName(c, true, l);
    if (k.isInterface() || java.lang.reflect.Modifier.isAbstract(k.getModifiers())) return null;
    try {
      return k.getDeclaredConstructor().newInstance();
    } catch (InvocationTargetException e) {
      throw e.getCause();
    }
  }

  static URL url(Path p) throws Exception { return p.toUri().toURL(); }
}
