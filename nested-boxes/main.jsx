import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import App from "./nested-boxes.jsx";

createRoot(document.getElementById("root")).render(
  <StrictMode><App /></StrictMode>
);
