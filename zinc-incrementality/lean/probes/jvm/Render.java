import java.lang.classfile.*;
import java.lang.classfile.attribute.ConstantValueAttribute;
import java.lang.constant.*;
import java.nio.file.*;
import java.util.*;

import static java.lang.classfile.ClassFile.*;

/**
 * Renders each case of `lake exe jvmcases` to classfiles with the Classfile API (JDK 24+):
 * `out/<case>/{v0,v1,client,sites}/*.class`. Library and client classes come from the case's class
 * tables. `sites` has `Loads` (`ldc X.class` for each class the client loads) and one class
 * `Site<k>` per call site, with `static void run()` as javac compiles `C c = new R(); c.m();`.
 * A site `at X` is rendered as `static void site$k()` in the client class `X`, which `Site<k>`
 * calls.
 *
 * Methods log their owner to `ProbeLog`. A `String` field holds its owner's name (instance fields
 * set by the constructor, static ones by `ConstantValue`), and a get logs it; a put stores "put"
 * and leaves the receiver in `ProbeLog.obj` for `Run` to find which class's field changed.
 *
 * Usage: java Render.java cases.jsonl out
 */
public class Render {
  static final int VERSION = 65; // Java 21, so the classfiles also run on JDK 21

  static final ClassDesc OBJECT = ClassDesc.of("java.lang.Object");
  static final ClassDesc STRING = ClassDesc.of("java.lang.String");
  static final ClassDesc LOG = ClassDesc.of("ProbeLog");
  static final MethodTypeDesc VOID = MethodTypeDesc.of(ConstantDescs.CD_void);
  static final MethodTypeDesc RAN = MethodTypeDesc.of(ConstantDescs.CD_void, STRING);

  public static void main(String[] args) throws Exception {
    Path out = Path.of(args[1]);
    for (String line : Files.readAllLines(Path.of(args[0]))) {
      if (line.isBlank()) continue;
      Map<String, Object> k = Json.obj(Json.parse(line));
      Path dir = out.resolve((String) k.get("name"));
      List<Map<String, Object>> sites = Json.objs(k.get("sites"));
      // Sites `at X`, by class: the index of the site and the inner site.
      Map<String, Map<Integer, Map<String, Object>>> at = new HashMap<>();
      for (int i = 0; i < sites.size(); i++) {
        Map<String, Object> s = sites.get(i);
        if (s.get("op").equals("at")) at.computeIfAbsent((String) s.get("cls"), x -> new TreeMap<>()).put(i, Json.obj(s.get("site")));
      }
      for (String t : List.of("v0", "v1", "client")) {
        for (Map<String, Object> c : Json.objs(k.get(t))) {
          String name = (String) c.get("name");
          Map<Integer, Map<String, Object>> extra = t.equals("client") ? at.getOrDefault(name, Map.of()) : Map.of();
          write(dir.resolve(t), name, renderClass(c, extra));
        }
      }
      write(dir.resolve("sites"), "Loads", renderLoads(Json.arr(k.get("loads"))));
      for (int i = 0; i < sites.size(); i++) write(dir.resolve("sites"), "Site" + i, renderSite("Site" + i, i, sites.get(i)));
    }
  }

  static void write(Path dir, String name, byte[] bytes) throws Exception {
    Path p = dir.resolve(name.replace('.', '/') + ".class");
    Files.createDirectories(p.getParent());
    Files.write(p, bytes);
  }

  static boolean bool(Map<String, Object> m, String k) { return Boolean.TRUE.equals(m.get(k)); }

  static int access(Map<String, Object> m) {
    return switch ((String) m.get("access")) {
      case "public" -> ACC_PUBLIC;
      case "protected" -> ACC_PROTECTED;
      case "private" -> ACC_PRIVATE;
      default -> 0;
    };
  }

  static byte[] renderClass(Map<String, Object> c, Map<Integer, Map<String, Object>> sites) {
    String name = (String) c.get("name");
    boolean itf = bool(c, "interface");
    String sup = (String) c.get("super");
    ClassDesc self = ClassDesc.of(name);
    ClassDesc superDesc = sup == null || itf ? OBJECT : ClassDesc.of(sup);
    List<Map<String, Object>> fields = Json.objs(c.get("fields"));
    return ClassFile.of().build(self, cb -> {
      cb.withVersion(VERSION, 0);
      int flags = bool(c, "public") ? ACC_PUBLIC : 0;
      if (itf) flags |= ACC_INTERFACE | ACC_ABSTRACT;
      else {
        flags |= ACC_SUPER;
        if (bool(c, "abstract")) flags |= ACC_ABSTRACT;
        if (bool(c, "final")) flags |= ACC_FINAL;
      }
      cb.withFlags(flags);
      cb.withSuperclass(superDesc);
      List<ClassDesc> is = new ArrayList<>();
      for (Object i : Json.arr(c.get("ifaces"))) is.add(ClassDesc.of((String) i));
      cb.withInterfaceSymbols(is);
      for (Map<String, Object> f : fields) {
        boolean st = bool(f, "static");
        int ff = access(f) | (st ? ACC_STATIC : 0) | (bool(f, "final") ? ACC_FINAL : 0);
        ClassDesc fd = ClassDesc.ofDescriptor((String) f.get("desc"));
        cb.withField((String) f.get("name"), fd, fb -> {
          fb.withFlags(ff);
          if (st) fb.with(ConstantValueAttribute.of(name));
        });
      }
      if (!itf) {
        cb.withMethodBody(ConstantDescs.INIT_NAME, VOID, ACC_PUBLIC, b -> {
          b.aload(0).invokespecial(superDesc, ConstantDescs.INIT_NAME, VOID);
          for (Map<String, Object> f : fields) {
            if (!bool(f, "static")) b.aload(0).ldc(name).putfield(self, (String) f.get("name"), ClassDesc.ofDescriptor((String) f.get("desc")));
          }
          b.return_();
        });
      }
      for (Map<String, Object> m : Json.objs(c.get("methods"))) {
        MethodTypeDesc d = MethodTypeDesc.ofDescriptor((String) m.get("desc"));
        int mf = access(m);
        if (bool(m, "static")) mf |= ACC_STATIC;
        if (bool(m, "final")) mf |= ACC_FINAL;
        if (bool(m, "abstract")) {
          cb.withMethod((String) m.get("name"), d, mf | ACC_ABSTRACT, mb -> {});
        } else {
          cb.withMethodBody((String) m.get("name"), d, mf, b -> {
            b.ldc(name).invokestatic(LOG, "ran", RAN);
            if (d.returnType().equals(ConstantDescs.CD_void)) b.return_();
            else b.iconst_0().ireturn();
          });
        }
      }
      sites.forEach((i, s) -> cb.withMethodBody("site$" + i, VOID, ACC_PUBLIC | ACC_STATIC, b -> {
        emit(b, self, s);
        b.return_();
      }));
    });
  }

  static byte[] renderLoads(List<Object> loads) {
    return ClassFile.of().build(ClassDesc.of("Loads"), cb -> {
      cb.withVersion(VERSION, 0);
      cb.withFlags(ACC_PUBLIC | ACC_SUPER);
      cb.withMethodBody("run", VOID, ACC_PUBLIC | ACC_STATIC, b -> {
        for (Object x : loads) b.ldc(ClassDesc.of((String) x)).pop();
        b.return_();
      });
    });
  }

  static CodeBuilder newObj(CodeBuilder b, ClassDesc r) {
    return b.new_(r).dup().invokespecial(r, ConstantDescs.INIT_NAME, VOID);
  }

  static void popResult(CodeBuilder b, MethodTypeDesc d) {
    if (!d.returnType().equals(ConstantDescs.CD_void)) b.pop();
  }

  /** The site's code; `self` is the class it is in. */
  static void emit(CodeBuilder b, ClassDesc self, Map<String, Object> s) {
    String op = (String) s.get("op");
    ClassDesc owner = ClassDesc.of((String) s.get("owner"));
    String n = (String) s.get("name");
    String desc = (String) s.get("desc");
    ClassDesc recv = s.get("recv") == null ? null : ClassDesc.of((String) s.get("recv"));
    switch (op) {
      case "invokestatic" -> { MethodTypeDesc d = MethodTypeDesc.ofDescriptor(desc); b.invokestatic(owner, n, d, false); popResult(b, d); }
      case "invokestaticIface" -> { MethodTypeDesc d = MethodTypeDesc.ofDescriptor(desc); b.invokestatic(owner, n, d, true); popResult(b, d); }
      case "invokevirtual" -> { MethodTypeDesc d = MethodTypeDesc.ofDescriptor(desc); newObj(b, recv).invokevirtual(owner, n, d); popResult(b, d); }
      case "invokeinterface" -> { MethodTypeDesc d = MethodTypeDesc.ofDescriptor(desc); newObj(b, recv).invokeinterface(owner, n, d); popResult(b, d); }
      case "invokespecial" -> {
        MethodTypeDesc d = MethodTypeDesc.ofDescriptor(desc);
        newObj(b, self).invokespecial(owner, n, d, bool(s, "iface"));
        popResult(b, d);
      }
      case "new" -> newObj(b, owner).pop();
      case "getfield" -> newObj(b, recv).getfield(owner, n, ClassDesc.ofDescriptor(desc)).invokestatic(LOG, "ran", RAN);
      case "putfield" -> newObj(b, recv).dup().putstatic(LOG, "obj", OBJECT).ldc("put").putfield(owner, n, ClassDesc.ofDescriptor(desc));
      case "getstatic" -> b.getstatic(owner, n, ClassDesc.ofDescriptor(desc)).invokestatic(LOG, "ran", RAN);
      case "putstatic" -> b.ldc("put").putstatic(owner, n, ClassDesc.ofDescriptor(desc));
      default -> throw new IllegalArgumentException(op);
    }
  }

  static byte[] renderSite(String name, int i, Map<String, Object> s) {
    return ClassFile.of().build(ClassDesc.of(name), cb -> {
      cb.withVersion(VERSION, 0);
      cb.withFlags(ACC_PUBLIC | ACC_SUPER);
      cb.withMethodBody("run", VOID, ACC_PUBLIC | ACC_STATIC, b -> {
        if (s.get("op").equals("at")) b.invokestatic(ClassDesc.of((String) s.get("cls")), "site$" + i, VOID, false);
        else emit(b, ClassDesc.of(name), s);
        b.return_();
      });
    });
  }
}
