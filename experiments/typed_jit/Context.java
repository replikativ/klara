package klara.typedprobe;

/** Narrow probe token. A real Klara context also carries basis, mint,
 * continuation, cache, feedback and authority references. */
public record Context(String gValueId) {}
