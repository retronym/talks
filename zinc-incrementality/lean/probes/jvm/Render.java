import java.lang.classfile.*;
import java.lang.constant.*;
import java.lang.reflect.AccessFlag;
import java.nio.file.*;
import java.util.*;

import static java.lang.classfile.ClassFile.*;

/**
 * Renders each case of `lake exe jvmcases` to classfiles with the Classfile API (JDK 24+):
 * `out/<case>/{v0,v1,client,sites}/*.class`. Library and client classes come from the case's class
 * tables; `sites` has one class `Site<k>` per call site, with `static void run(Object recv)`.
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
  static final MethodTypeDesc RUN = MethodTypeDesc.of(ConstantDescs.CD_void, OBJECT);

  public static void main(String[] args) throws Exception {
    Path out = Path.of(args[1]);
    for (String line : Files.readAllLines(Path.of(args[0]))) {
      if (line.isBlank()) continue;
      Map<String, Object> k = Json.obj(Json.parse(line));
      Path dir = out.resolve((String) k.get("name"));
      for (String t : List.of("v0", "v1", "client")) {
        for (Map<String, Object> c : Json.objs(k.get(t))) write(dir.resolve(t), (String) c.get("name"), renderClass(c));
      }
      List<Map<String, Object>> sites = Json.objs(k.get("sites"));
      for (int i = 0; i < sites.size(); i++) write(dir.resolve("sites"), "Site" + i, renderSite("Site" + i, sites.get(i)));
    }
  }

  static void write(Path dir, String name, byte[] bytes) throws Exception {
    Path p = dir.resolve(name.replace('.', '/') + ".class");
    Files.createDirectories(p.getParent());
    Files.write(p, bytes);
  }

  static boolean bool(Map<String, Object> m, String k) { return Boolean.TRUE.equals(m.get(k)); }

  static byte[] renderClass(Map<String, Object> c) {
    String name = (String) c.get("name");
    boolean itf = bool(c, "interface");
    String sup = (String) c.get("super");
    ClassDesc superDesc = sup == null || itf ? OBJECT : ClassDesc.of(sup);
    return ClassFile.of().build(ClassDesc.of(name), cb -> {
      cb.withVersion(VERSION, 0);
      int flags = ACC_PUBLIC;
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
      if (!itf) {
        cb.withMethodBody(ConstantDescs.INIT_NAME, VOID, ACC_PUBLIC, b -> b
            .aload(0).invokespecial(superDesc, ConstantDescs.INIT_NAME, VOID).return_());
      }
      for (Map<String, Object> m : Json.objs(c.get("methods"))) {
        MethodTypeDesc d = MethodTypeDesc.ofDescriptor((String) m.get("desc"));
        int mf = ACC_PUBLIC;
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
    });
  }

  static byte[] renderSite(String name, Map<String, Object> s) {
    String op = (String) s.get("op");
    ClassDesc owner = ClassDesc.of((String) s.get("owner"));
    String mname = (String) s.get("name");
    MethodTypeDesc d = s.get("desc") == null ? null : MethodTypeDesc.ofDescriptor((String) s.get("desc"));
    return ClassFile.of().build(ClassDesc.of(name), cb -> {
      cb.withVersion(VERSION, 0);
      cb.withFlags(ACC_PUBLIC | ACC_SUPER);
      cb.withMethodBody("run", RUN, ACC_PUBLIC | ACC_STATIC, b -> {
        switch (op) {
          case "invokestatic" -> b.invokestatic(owner, mname, d, false);
          case "invokevirtual" -> b.aload(0).checkcast(owner).invokevirtual(owner, mname, d);
          case "invokeinterface" -> b.aload(0).checkcast(owner).invokeinterface(owner, mname, d);
          case "new" -> b.new_(owner).dup().invokespecial(owner, ConstantDescs.INIT_NAME, VOID).pop();
          default -> throw new IllegalArgumentException(op);
        }
        if (d != null && !d.returnType().equals(ConstantDescs.CD_void)) b.pop();
        b.return_();
      });
    });
  }
}
