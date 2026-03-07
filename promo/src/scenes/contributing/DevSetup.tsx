import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const commands = [
  { cmd: "python -m pip install -e \".[dev,runtime]\"", label: "Install deps" },
  { cmd: "pytest tests/ -v", label: "Run tests" },
  { cmd: "ruff check swarm/ tests/", label: "Lint" },
  { cmd: "mypy swarm/", label: "Type check" },
];

export const DevSetup: React.FC = () => {
  const frame = useCurrentFrame();

  const headerProgress = spring({ frame, fps: 30, config: { damping: 200 } });

  return (
    <AbsoluteFill
      style={{
        background: colors.bg,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
        padding: 80,
      }}
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundImage: `
            linear-gradient(${colors.gridLine} 1px, transparent 1px),
            linear-gradient(90deg, ${colors.gridLine} 1px, transparent 1px)
          `,
          backgroundSize: "80px 80px",
          opacity: 0.2,
        }}
      />

      <div
        style={{
          fontSize: 28,
          fontWeight: 600,
          color: colors.accent,
          letterSpacing: "0.15em",
          textTransform: "uppercase",
          opacity: headerProgress,
          marginBottom: 8,
        }}
      >
        Step 2
      </div>

      <div
        style={{
          fontSize: 64,
          fontWeight: 800,
          color: colors.text,
          opacity: headerProgress,
          marginBottom: 50,
        }}
      >
        Set Up Your Environment
      </div>

      <div
        style={{
          background: `${colors.accent}08`,
          border: `1px solid ${colors.accent}30`,
          borderRadius: 16,
          padding: "40px 50px",
          maxWidth: 900,
          width: "100%",
        }}
      >
        <div
          style={{
            display: "flex",
            alignItems: "center",
            gap: 12,
            marginBottom: 30,
            fontSize: 20,
            color: colors.textDim,
            fontFamily: fonts.mono,
          }}
        >
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: "50%",
              background: colors.danger,
            }}
          />
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: "50%",
              background: colors.warning,
            }}
          />
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: "50%",
              background: colors.success,
            }}
          />
          <span style={{ marginLeft: 12 }}>terminal</span>
        </div>

        {commands.map((item, i) => {
          const delay = 20 + i * 30;
          const progress = spring({
            frame: frame - delay,
            fps: 30,
            config: { damping: 200 },
          });
          const p = Math.max(0, progress);

          // Typing effect
          const typingStart = delay + 5;
          const charCount = Math.min(
            item.cmd.length,
            Math.max(0, Math.floor((frame - typingStart) * 1.5)),
          );
          const displayCmd = item.cmd.slice(0, charCount);
          const showCursor = frame >= typingStart && charCount < item.cmd.length;

          return (
            <div
              key={i}
              style={{
                display: "flex",
                alignItems: "center",
                gap: 16,
                marginBottom: 20,
                opacity: p,
              }}
            >
              <span
                style={{
                  fontSize: 14,
                  color: colors.textMuted,
                  fontFamily: fonts.mono,
                  minWidth: 100,
                  textAlign: "right",
                }}
              >
                {item.label}
              </span>
              <span
                style={{
                  color: colors.success,
                  fontFamily: fonts.mono,
                  fontSize: 18,
                }}
              >
                $
              </span>
              <span
                style={{
                  color: colors.text,
                  fontFamily: fonts.mono,
                  fontSize: 22,
                }}
              >
                {displayCmd}
                {showCursor && (
                  <span
                    style={{
                      color: colors.accent,
                      opacity: Math.sin(frame * 0.3) > 0 ? 1 : 0,
                    }}
                  >
                    |
                  </span>
                )}
              </span>
            </div>
          );
        })}
      </div>

      <div
        style={{
          fontSize: 22,
          color: colors.textDim,
          marginTop: 40,
          opacity: Math.max(
            0,
            spring({
              frame: frame - 120,
              fps: 30,
              config: { damping: 200 },
            }),
          ),
          fontStyle: "italic",
        }}
      >
        Python 3.10+ required
      </div>
    </AbsoluteFill>
  );
};
